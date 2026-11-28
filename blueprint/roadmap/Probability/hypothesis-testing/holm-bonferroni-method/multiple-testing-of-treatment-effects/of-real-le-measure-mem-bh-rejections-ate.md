# Benjamini–Hochberg power in terms of the average treatment effect

For endpoints with observed outcomes $Y_j$ and scales $\kappa_j$, let $\theta_j = \exp(\kappa_j\Delta_j)$, where $\Delta_j$ is the inverse-probability-weighted contrast of $Y_j$, and $p_j = \max(U_{c(j)}, 0)^{\theta_j}$ the ATE Lehmann p-values. If endpoint $j$ is strongly ignorable given a finitely valued $X$ with measurable integrable potential outcomes and $U_{c(j)}$ is uniform, then Benjamini–Hochberg at level $q \in [0, 1]$ rejects $j$ with probability at least $(q/m)^{\exp(-\kappa_j\mathbb{E}[Y_{1j} - Y_{0j}])}$.
