# Power of an average-treatment-effect Lehmann test

For endpoints with observed outcomes $Y_j$ and scales $\kappa_j$, let $\theta_j = \exp(\kappa_j\Delta_j)$, where $\Delta_j$ is the inverse-probability-weighted contrast of $Y_j$, and $p_j = \max(U_{c(j)}, 0)^{\theta_j}$ the ATE Lehmann p-values. If $U_{c(j)}$ is uniform on $[0, 1]$, then $P(p_j \le t) = t^{\exp(-\kappa_j\Delta_j)}$ for $t \in [0, 1]$.
