# The RBAC$_0$ model: users, roles, permissions and sessions

The base model RBAC$_0$ of role-based access control has the following components:

- sets $U$, $R$, $P$ and $S$ of users, roles, permissions and sessions;
- a many-to-many permission-to-role assignment relation $PA \subseteq P \times R$ and a many-to-many user-to-role assignment relation $UA \subseteq U \times R$;
- a function $\mathit{user} : S \to U$ mapping each session $s_i$ to the single user $\mathit{user}(s_i)$, constant for the lifetime of the session;
- a function $\mathit{roles} : S \to 2^R$ mapping each session $s_i$ to a set of roles $\mathit{roles}(s_i) \subseteq \{r \mid (\mathit{user}(s_i), r) \in UA\}$, which can change with time.

Session $s_i$ has the permissions $\bigcup_{r \in \mathit{roles}(s_i)} \{p \mid (p, r) \in PA\}$. Permissions are uninterpreted symbols; a session plays the part of a
subject in the access-control literature, and a user may have several sessions active at once.

## Sources

- R. S. Sandhu, E. J. Coyne, H. L. Feinstein and C. E. Youman, "Role-based access control models", *IEEE Computer* 29(2):38–47, 1996, copy at <https://csrc.nist.gov/CSRC/media/Projects/Role-Based-Access-Control/documents/sandhu96.pdf>: Section 4.1, Definition 1 (RBAC$_0$).
