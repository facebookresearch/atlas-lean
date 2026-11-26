# Private empirical risk minimization and private stochastic convex optimization

Let $\mathcal{W} \subseteq \mathbb{R}^d$ be convex with diameter $D$, let $\ell(w, z)$ be convex and $L$-Lipschitz in $w$ for every data point $z$, let $\hat F_S(w) = \frac1n\sum_i \ell(w, z_i)$ be the empirical risk of a dataset $S$ and $F(w) = \mathbb{E}_{z \sim \mathcal{D}}[\ell(w,z)]$ the population risk. A mechanism $A$ for **private empirical risk minimization** is an $(\varepsilon,\delta)$-differentially private map from datasets to $\mathcal{W}$, measured by its **excess empirical risk** $\mathbb{E}[\hat F_S(A(S))] - \min_{w \in \mathcal{W}} \hat F_S(w)$. In **private stochastic convex optimization** (DP-SCO), $S \sim \mathcal{D}^n$ and $A$ is measured by its **excess population risk** $\mathbb{E}[F(A(S))] - \min_{w \in \mathcal{W}} F(w)$, while privacy is still required for every pair of neighbouring datasets.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Expected risk](../../machine-learning/generalization-bounds-and-concentration/risk.md)
- [Empirical risk](../../machine-learning/generalization-bounds-and-concentration/empirical-risk.md)

## Sources

- R. Bassily, A. Smith, A. Thakurta, "Differentially Private Empirical Risk Minimization: Efficient Algorithms and Tight Error Bounds", FOCS (2014), arXiv:1405.7085.
- R. Bassily, V. Feldman, K. Talwar, A. Thakurta, "Private Stochastic Convex Optimization with Optimal Rates", NeurIPS (2019), arXiv:1908.09970.
