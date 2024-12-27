#include <stdio.h>
#include <stdlib.h>
#include<string.h>
#include <stdbool.h>

#define MAX_USERS 5000
#define MAX_PERMISSIONS 5000
#define MAX_ROLES 800

int UPA[MAX_USERS][MAX_PERMISSIONS] = {0}; // User-Permission Assignment matrix
int UA[MAX_USERS][MAX_ROLES] = {0};        // User-Role Assignment matrix
int PA[MAX_ROLES][MAX_PERMISSIONS] = {0};  // Permission-Role Assignment matrix

int num_users, num_permissions, num_roles=0;
int role_usage_constraint, permission_distribution_constraint;

int UserRoleCount[MAX_USERS] = {0};
int PermRoleCount[MAX_PERMISSIONS] = {0};
int UC[MAX_USERS][MAX_PERMISSIONS] = {0}; // Uncovered edges for users
int V[MAX_USERS][MAX_PERMISSIONS] = {0}; // Incident edges for users

bool is_redundant_role(int U[], int P[]) {
    for (int r = 0; r < num_roles; r++) {
        bool is_subset = true;
        for (int u = 0; u < num_users; u++) {
            if (U[u] && !UA[u][r]) {
                is_subset = false;
                break;
            }
        }
        if (is_subset) {
            for (int p = 0; p < num_permissions; p++) {
                if (P[p] && !PA[r][p]) {
                    is_subset = false;
                    break;
                }
            }
        }
        if (is_subset) {
            return true;
        }
    }
    return false;
}

void Form_Role(int v, int U[], int P[]) {
    U[v] = 1;
    UserRoleCount[v]++;
    for (int p = 0; p < num_permissions; p++) {
        if (UC[v][p] && PermRoleCount[p] <= permission_distribution_constraint - 1) {
            P[p] = 1;
            PermRoleCount[p]++;
        }
    }

    //if role contains no permissions then don't add it 
    bool isempty=true;
    for(int i=0;i<num_permissions;i++){
        if(P[i]==1){
            isempty=false;
            break;
        }
    }
    if(isempty){
        UserRoleCount[v]--;
        return;
    }

    for (int u = 0; u < num_users; u++) {
        if (u != v) {
            int is_subset = 1;
            for (int p = 0; p < num_permissions; p++) {
                if (P[p] && !V[u][p]) {
                    is_subset = 0;
                    break;
                }
            }
            if (is_subset && UserRoleCount[u] < role_usage_constraint - 1) {
                int has_common_permission = 0;
                for (int p = 0; p < num_permissions; p++) {
                    if (UC[u][p] && P[p]) {
                        has_common_permission = 1;
                        break;
                    }
                }
                if (has_common_permission) {
                    U[u] = 1;
                    UserRoleCount[u]++;
                }
            } else if (is_subset && UserRoleCount[u] == role_usage_constraint - 1) {
                int all_in_P = 1;
                for (int p = 0; p < num_permissions; p++) {
                    if (UC[u][p] && !P[p]) {
                        all_in_P = 0;
                        break;
                    }
                }
                if (all_in_P) {
                    U[u] = 1;
                    UserRoleCount[u]++;
                }
            }
        }
    }

    if (!is_redundant_role(U, P)){
        // Form a biclique with U and P
        for (int u = 0; u < num_users; u++){
            if (U[u]){
                for (int p = 0; p < num_permissions; p++){
                    if (P[p]){
                        UA[u][num_roles] = 1;
                        PA[num_roles][p] = 1;
                        UC[u][p] = 0;
                    }
                }
            }
        }
        num_roles++;
    }
    
}

void Dual_Form_Role(int v, int U[], int P[]) {
    P[v] = 1;
    PermRoleCount[v]++;
    for (int u = 0; u < num_users; u++) {
        if (UC[u][v] && UserRoleCount[u] <= role_usage_constraint - 1) {
            U[u] = 1;
            UserRoleCount[u]++;
        }
    }

     // if role contains no users then don't add it 
    bool isempty = true;
    for (int i = 0; i < num_users; i++) {
        if (U[i] == 1) {
            isempty = false;
            break;
        }
    }
    if (isempty) {
        PermRoleCount[v]--;
        return;
    }

    for (int p = 0; p < num_permissions; p++) {
        if (p != v) {
            int is_subset = 1;
            for (int u = 0; u < num_users; u++) {
                if (U[u] && !V[u][p]) {
                    is_subset = 0;
                    break;
                }
            }
            if (is_subset && PermRoleCount[p] < permission_distribution_constraint - 1) {
                int has_common_user = 0;
                for (int u = 0; u < num_users; u++) {
                    if (UC[u][p] && U[u]) {
                        has_common_user = 1;
                        break;
                    }
                }
                if (has_common_user) {
                    P[p] = 1;
                    PermRoleCount[p]++;
                }
            } else if (is_subset && PermRoleCount[p] == permission_distribution_constraint - 1) {
                int all_in_U = 1;
                for (int u = 0; u < num_users; u++) {
                    if (UC[u][p] && !U[u]) {
                        all_in_U = 0;
                        break;
                    }
                }
                if (all_in_U) {
                    P[p] = 1;
                    PermRoleCount[p]++;
                }
            }
        }
    }

    if (!is_redundant_role(U, P)) {
        // Form a biclique with U and P
        for (int u = 0; u < num_users; u++) {
            if (U[u]) {
                for (int p = 0; p < num_permissions; p++) {
                    if (P[p]) {
                        UA[u][num_roles] = 1;
                        PA[num_roles][p] = 1;
                        UC[u][p] = 0;
                    }
                }
            }
        }
        num_roles++;
    }
}

int select_vertex() {
    // Heuristic: Node with the minimum number of uncovered incident edges giving priority to user
    int min_edges = MAX_USERS * MAX_PERMISSIONS;
    int selected_vertex = -1;
    int is_user = 1;

    for (int u = 0; u < num_users; u++) {
        if (UserRoleCount[u] <= role_usage_constraint - 1) {
            int uncovered_edges = 0;
            for (int p = 0; p < num_permissions; p++) {
                if (UC[u][p]) {
                    uncovered_edges++;
                }
            }
            if (uncovered_edges < min_edges && uncovered_edges != 0) {
                min_edges = uncovered_edges;
                selected_vertex = u;
                is_user = 1;
            }
        }
    }

    for (int p = 0; p < num_permissions; p++) {
        if (PermRoleCount[p] < permission_distribution_constraint - 1) {
            int uncovered_edges = 0;
            for (int u = 0; u < num_users; u++) {
                if (UC[u][p]) {
                    uncovered_edges++;
                }
            }
            if (uncovered_edges < min_edges && uncovered_edges != 0) {
                min_edges = uncovered_edges;
                selected_vertex = p;
                is_user = 0;
            }
        }
    }
    // printf("\nSelected vertex: %d\n", selected_vertex);
    return is_user ? selected_vertex : -selected_vertex;
}

int select_vertex_max_uncovered() {
    // Heuristic: Node with the maximum number of uncovered incident edges
    int max_edges = -1;
    int selected_vertex = -1;
    int is_user = 1;

    for (int u = 0; u < num_users; u++) {
        if (UserRoleCount[u] == role_usage_constraint - 1) {
            int uncovered_edges = 0;
            for (int p = 0; p < num_permissions; p++) {
                if (UC[u][p]) {
                    uncovered_edges++;
                }
            }
            if (uncovered_edges > max_edges && uncovered_edges != 0) {
                max_edges = uncovered_edges;
                selected_vertex = u;
                is_user = 1;
            }
        }
    }

    for (int p = 0; p < num_permissions; p++) {
        if (PermRoleCount[p] == permission_distribution_constraint - 1) {
            int uncovered_edges = 0;
            for (int u = 0; u < num_users; u++) {
                if (UC[u][p]) {
                    uncovered_edges++;
                }
            }
            if (uncovered_edges > max_edges && uncovered_edges != 0) {
                max_edges = uncovered_edges;
                selected_vertex = p;
                is_user = 0;
            }
        }
    }
    // printf("\nSelected dual vertex: %d\n", selected_vertex);
    return is_user ? selected_vertex : -selected_vertex;
}

void Enforce_Role_And_Permission_Constraints() {

    // Initialize UC and V matrices
    for (int u = 0; u < num_users; u++) {
        for (int p = 0; p < num_permissions; p++) {
            if (UPA[u][p] == 1) {
                UC[u][p] = 1;
                V[u][p] = 1;
            }
        }
    }

    // Phase 1
    for (int u = 0; u < num_users; u++) {
        for (int p = 0; p < num_permissions; p++) {
            if ((UserRoleCount[u] < role_usage_constraint - 1 && UC[u][p]) || (PermRoleCount[p] < permission_distribution_constraint - 1 && UC[u][p])) {
                int U[MAX_USERS] = {0};
                int P[MAX_PERMISSIONS] = {0};
                // printf("\nu=%d p=%d",u,p);
                int selected_vertex = select_vertex();

                if (selected_vertex >= 0) {
                    Form_Role(selected_vertex, U, P);
                } else {
                    Dual_Form_Role(-selected_vertex, U, P);
                }
                //debug
                // for(int i = 0; i<MAX_USERS; i++){
                //     for(int j=0;j<MAX_PERMISSIONS;j++){
                //         printf("%d ",UC[i][j]);
                //     }
                //     printf("\n");
                // }
                // printf("\n");
                // for(int i = 0; i<MAX_USERS; i++) printf("%d ",UserRoleCount[i]);
                // printf("\n");
                // for(int i = 0; i<MAX_PERMISSIONS; i++) printf("%d ",PermRoleCount[i]);
                // printf("\n");

            }
        }
    }

    // Phase 2
    for (int u = 0; u < num_users; u++){
        for (int p = 0; p < num_permissions; p++){
            if ((UserRoleCount[u] == role_usage_constraint - 1 && UC[u][p]) || (PermRoleCount[p] == permission_distribution_constraint - 1 && UC[u][p])){
                int U[MAX_USERS] = {0};
                int P[MAX_PERMISSIONS] = {0};
                // printf("\nu=%d p=%d",u,p);
                int selected_vertex = select_vertex_max_uncovered();

                // If the selected vertex is a user
                if (selected_vertex >= 0){
                    int v = selected_vertex;
                    for (int p = 0; p < num_permissions; p++){
                        P[p] = UC[v][p];
                    }
                    bool can_form_role = true;
                    for (int p = 0; p < num_permissions; p++){
                        if (P[p] && PermRoleCount[p] > permission_distribution_constraint - 1){
                            can_form_role = false;
                            break;
                        }
                    }

                    if (can_form_role){
                        Form_Role2(v, U, P);
                    }
                    
                    // //debug
                    // for(int i = 0; i<MAX_USERS; i++){
                    //     for(int j=0;j<MAX_PERMISSIONS;j++){
                    //         printf("%d ",UC[i][j]);
                    //     }
                    //     printf("\n");
                    // }
                    // printf("\n");
                    // for(int i = 0; i<MAX_USERS; i++) printf("%d ",UserRoleCount[i]);
                    // printf("\n");
                    // for(int i = 0; i<MAX_PERMISSIONS; i++) printf("%d ",PermRoleCount[i]);
                    // printf("\n");
                }
                else {
                    int v = -selected_vertex;
                    // Set U = UC[v]
                    for (int u = 0; u < num_users; u++) {
                        U[u] = UC[u][v];
                    }
                    // Check if UserRoleCount[u] <= role_usage_constraint - 1 for all u in U
                    bool can_form_role = true;
                    for (int u = 0; u < num_users; u++) {
                        if (U[u] && UserRoleCount[u] > role_usage_constraint - 1) {
                            can_form_role = false;
                            break;
                        }
                    }

                    if (can_form_role) {
                        Dual_Form_Role2(v, U, P);
                    }
                }
            }
        }
    }

    // Check if there are any uncovered edges left
    for (int u = 0; u < num_users; u++) {
        for (int p = 0; p < num_permissions; p++) {
            if (UC[u][p]) {
                printf("The given set of constraints cannot be enforced\n");
                return;
            }
        }
    }
}

void readUPA(char *filename) {
    FILE *file = fopen(filename, "r");
    if (file == NULL) {
        perror("Failed to open file");
        exit(1);
    }

    fscanf(file, "%d", &num_users);
    fscanf(file, "%d", &num_permissions);

    int user, permission;
    while (fscanf(file, "%d %d", &user, &permission) != EOF) {
        UPA[user - 1][permission - 1] = 1;
    }
    fclose(file);
}

void printMatrices() {
    printf("User-Role Assignment Matrix (UA):\n");
    for (int i = 0; i < num_users; i++) {
        for (int j = 0; j < num_roles; j++) {
            printf("%d ", UA[i][j]);
        }
        printf("\n");
    }

    printf("\nRole-Permission Assignment Matrix (PA):\n");
    for (int i = 0; i < num_roles; i++) {
        for (int j = 0; j < num_permissions; j++) {
            printf("%d ", PA[i][j]);
        }
        printf("\n");
    }
}

void writeUA(char *dataset_name) {
    char filename[50];
    sprintf(filename, "%s_UA.txt", dataset_name);
    FILE *file = fopen(filename, "w");
    if (file == NULL) {
        perror("Failed to create UA file");
        exit(1);
    }

    fprintf(file, "%d\n", num_users);
    fprintf(file, "%d\n", num_roles);
    for (int u = 0; u < num_users; u++) {
        for (int r = 0; r < num_roles; r++) {
            fprintf(file, "%d ", UA[u][r]);
        }
        fprintf(file, "\n");
    }
    fclose(file);
}

void writePA(char *dataset_name) {
    char filename[50];
    sprintf(filename, "%s_PA.txt", dataset_name);
    FILE *file = fopen(filename, "w");
    if (file == NULL) {
        perror("Failed to create PA file");
        exit(1);
    }

    fprintf(file, "%d\n", num_roles);
    fprintf(file, "%d\n", num_permissions);
    for (int r = 0; r < num_roles; r++) {
        for (int p = 0; p < num_permissions; p++) {
            fprintf(file, "%d ", PA[r][p]);
        }
        fprintf(file, "\n");
    }
    fclose(file);
}

int main() {
    char filename[100];
    printf("Enter the name of the UPA matrix file: ");
    scanf("%s", filename);

    readUPA(filename);

    // for(int i=0;i<MAX_USERS;i++){
    //     for(int j=0;j<MAX_PERMISSIONS;j++){
    //         printf("%d ",UPA[i][j]);
    //     }
    //     printf("\n");
    // }

    // Extract dataset name from filename
    char dataset_name[100];
    strcpy(dataset_name, filename);
    char *dot_position = strrchr(dataset_name, '.');
    if (dot_position != NULL) {
        *dot_position = '\0'; // Replace '.' with null terminator to get the dataset name
    }
    
    printf("Enter the value of the role-usage cardinality constraint: ");
    scanf("%d", &role_usage_constraint);
    printf("Enter the value of the permission-distribution cardinality constraint: ");
    scanf("%d", &permission_distribution_constraint);

    // Enforce constraints and generate roles
    Enforce_Role_And_Permission_Constraints();

    // Output the results
    printf("Number of roles = %d\n", num_roles);

    // printMatrices();

   // Write UA and PA matrices to files
    writeUA(dataset_name);
    writePA(dataset_name);
    

    return 0;
}
