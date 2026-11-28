# Power of a Lehmann p-value

Let $U_1, \dots, U_k$ be noise variables and $c$ a map from endpoints to clusters, and let endpoint $j$ report the Lehmann p-value $p_j = \max(U_{c(j)}, 0)^{\theta_j}$ with exponent $\theta_j$. Suppose $U_{c(j)}$ is uniform on $[0, 1]$. If $\theta_j > 0$, then $P(p_j \le t) = t^{1/\theta_j}$ for $t \in [0, 1]$.

## Sources

- Lehmann (1953), the alternatives `G = F ^ k`; for p-values, the Beta(`a`, 1) alternative of the beta-uniform mixture of Pounds & Morris (2003).
