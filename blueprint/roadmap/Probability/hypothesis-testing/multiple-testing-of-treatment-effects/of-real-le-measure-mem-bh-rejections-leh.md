# Benjamini–Hochberg power for Lehmann p-values

Let $U_1, \dots, U_k$ be noise variables and $c$ a map from endpoints to clusters, and let endpoint $j$ report the Lehmann p-value $p_j = \max(U_{c(j)}, 0)^{\theta_j}$ with exponent $\theta_j$. Suppose $U_{c(j)}$ is uniform on $[0, 1]$. If $\theta_j > 0$ and $q \in [0, 1]$, Benjamini–Hochberg at level $q$ rejects endpoint $j$ with probability at least $(q/m)^{1/\theta_j}$.
