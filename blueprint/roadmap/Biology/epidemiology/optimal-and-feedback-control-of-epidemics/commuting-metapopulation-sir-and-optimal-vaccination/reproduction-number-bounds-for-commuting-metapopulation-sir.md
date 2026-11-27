# Reproduction-number bounds for the day–night commuting metapopulation SIR model

Consider $K$ cities with populations $n_i$ and a row-stochastic commuting matrix $P = (p_{ij})$, where $p_{ij}$ is the fraction of residents of city $i$ who spend the day in city $j$. Let $\alpha(t) \in \{0,1\}$ be a daily periodic switch ($1$ at night, $0$ in the day). With effective daytime populations $P_j^{\mathrm{eff}} = \sum_k p_{kj} n_k$ and effective daytime prevalences $I_j^{\mathrm{eff}} = \frac{1}{P_j^{\mathrm{eff}}}\sum_k p_{kj} I_k n_k$, the model is

$$
\begin{aligned}
S_i' &= \mu - \alpha(t)\beta_i S_i I_i - (1 - \alpha(t)) S_i \sum_{j=1}^K \beta_j p_{ij} I_j^{\mathrm{eff}} - \mu S_i, \\
I_i' &= \alpha(t)\beta_i S_i I_i + (1 - \alpha(t)) S_i \sum_{j=1}^K \beta_j p_{ij} I_j^{\mathrm{eff}} - (\gamma + \mu) I_i, \\
R_i' &= \gamma I_i - \mu R_i,
\end{aligned}
$$

and the simplex $\{S_i + I_i + R_i = 1\}$ is positively invariant. Treat $\alpha \in [0,1]$ as the fraction of time spent at home (the time-averaged system). Let $\mathcal{R}_0^i = \beta_i/(\gamma + \mu)$ be the reproduction number of city $i$ in isolation and $\mathcal{R}_0$ the next-generation spectral radius of the whole system.

**Theorem.**

$$
\min_{1 \le i \le K} \Big[ \alpha\mathcal{R}_0^i + (1 - \alpha)\sum_{k=1}^K p_{ik}\mathcal{R}_0^k \Big] \ \le\ \mathcal{R}_0 \ \le\ \max_{1 \le i \le K} \Big[ \alpha\mathcal{R}_0^i + (1 - \alpha)\sum_{k=1}^K p_{ik}\mathcal{R}_0^k \Big].
$$

In particular $\min_i \mathcal{R}_0^i \le \mathcal{R}_0 \le \max_i \mathcal{R}_0^i$: commuting cannot push the network threshold outside the range of the isolated cities.

**Theorem (metropolitan area).** Suppose city $1$ is a capital whose residents stay at home, and every other city $i$ sends a fraction $p_{i1}$ to the capital and keeps $p_{ii} = 1 - p_{i1}$. Then

$$
\frac{\xi}{\gamma + \mu} \le \mathcal{R}_0 \le \frac{1}{\gamma + \mu}\Big( \xi + (1 - \alpha)\frac{\beta_1}{P_1^{\mathrm{eff}}}\sum_{i=1}^K n_i p_{i1}^2 \Big), \qquad \xi = \max_{i} \big[ \alpha\beta_i + (1 - \alpha) p_{ii}\beta_i (1 - \delta_{i1}) \big].
$$

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At the disease-free equilibrium $S_i = 1$, so $V = (\gamma+\mu)I$, and $FV^{-1} = \frac{1}{\gamma+\mu}\big(\alpha\,\mathrm{diag}(\beta) + (1-\alpha) P\, \mathrm{diag}(\beta)\, \mathrm{diag}(P^{\mathrm{eff}})^{-1} P^\top \mathrm{diag}(n)\big)$. This matrix is similar to a symmetric matrix, so its eigenvalues are real. Its row sums are the bracketed expressions in the first theorem, and the spectral radius of a nonnegative matrix lies between its minimum and maximum row sums. The metropolitan bound comes from splitting $FV^{-1}$ into a diagonal part, which gives $\xi$, and the rank-one contribution of commuting into the capital.

## Sources

- M. Soledad Aronna, Lucas Machado Moschen, "Optimal vaccination strategies on networks and in metropolitan areas", Infectious Disease Modelling 9 (2024), 1198–1222, <https://doi.org/10.1016/j.idm.2024.06.007>. Published version of arXiv:2402.00207, cited next; locators there refer to the arXiv version.
- Lucas Machado Moschen, María Soledad Aronna, "Optimal vaccination strategies on networks and in metropolitan areas", arXiv (2024). Theorem 2.1, Corollary 2.1, Theorem 2.2, Lemma A.1, Propositions B.1 and B.2. <https://doi.org/10.48550/arXiv.2402.00207>
