# The RBAC$_1$ model: role hierarchies

The model RBAC$_1$ extends [RBAC$_0$](rbac0-users-roles-permissions-and-sessions.md) as follows. $U$, $R$, $P$, $S$, $PA$, $UA$ and $\mathit{user}$ are unchanged, and

- $RH \subseteq R \times R$ is a partial order on $R$, the *role hierarchy* or role dominance relation, written $\ge$ (a senior role $r \ge r'$ inherits the permissions of the junior role $r'$);
- $\mathit{roles} : S \to 2^R$ is required to satisfy $\mathit{roles}(s_i) \subseteq \{r \mid \exists r' \ge r.\ (\mathit{user}(s_i), r') \in UA\}$, and session $s_i$ has the permissions
  $\bigcup_{r \in \mathit{roles}(s_i)} \{p \mid \exists r'' \le r.\ (p, r'') \in PA\}$.

So a user may establish a session with any combination of roles junior to roles the user is assigned to, and a session holds the permissions assigned to its
roles and to the roles junior to them.

## Depends on

- [The RBAC$_0$ model: users, roles, permissions and sessions](rbac0-users-roles-permissions-and-sessions.md)

## Sources

- R. S. Sandhu, E. J. Coyne, H. L. Feinstein and C. E. Youman, "Role-based access control models", *IEEE Computer* 29(2):38–47, 1996, copy at <https://csrc.nist.gov/CSRC/media/Projects/Role-Based-Access-Control/documents/sandhu96.pdf>: Section 4.2, "Role hierarchies", Definition 2 (RBAC$_1$).
