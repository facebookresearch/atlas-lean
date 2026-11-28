# Bonferroni power for Lehmann p-values

Let $U_1, \dots, U_k$ be noise variables and $c$ a map from endpoints to clusters, and let endpoint $j$ report the Lehmann p-value $p_j = \max(U_{c(j)}, 0)^{\theta_j}$ with exponent $\theta_j$. Suppose $U_{c(j)}$ is uniform on $[0, 1]$. If $\theta_j > 0$ and $\alpha \in [0, 1]$, the probability that Bonferroni at level $\alpha$ rejects endpoint $j$ is $(\alpha/m)^{1/\theta_j}$.
