# Multiple Poisson–Dirichlet diffusion and its stationary law

**Setting.** Rank the within-mark frequencies of the blockwise representation $Z^K_{h,i} = W_h \mathcal X_{h,i}$ in decreasing order and let the number $K$ of types per mark tend to infinity. The state space is a generalized Kingman simplex: $H$ ranked sequences $z_h = (z_{h,1} \ge z_{h,2} \ge \dots \ge 0)$ with $\sum_h \sum_i z_{h,i} = 1$.

**Theorem.**
1. If the ranked initial conditions converge, the ranked processes converge in distribution to a limit $Z$ with $Z_{h,\cdot}(t) = W_h(t)\, \mathcal X_h(t)$, where $W$ is the $H$-type Wright–Fisher diffusion with mutation parameters $\theta_1, \dots, \theta_H$ and $\mathcal X_h$ are independent infinitely-many-neutral-alleles (Poisson–Dirichlet) diffusions with parameters $\theta_h$, each time-changed by $\int_0^t W_h(s)^{-1} ds$. The associated martingale problem is well posed, and the generator of $Z$ is given explicitly on a domain of products $\prod_h |z_h|^{m^h_0} \Phi_{\mathbf m^h}(z_h)$ of symmetric moment functions.
2. The product law $\mu^* = \mathrm{Dir}_H(\theta_1, \dots, \theta_H) \otimes \bigotimes_{h=1}^H \mathrm{PD}(\theta_h)$ is invariant for $(W, \mathcal X_1, \dots, \mathcal X_H)$; consequently $Z$ started from the image of $\mu^*$ under $(w, x) \mapsto (w_h x_h)_h$, the *multiple Poisson–Dirichlet distribution*, is stationary. This law is also the $K \to \infty$ limit of the ranked $\mathrm{Dir}_{HK}(\theta_h/K)$ laws.
3. For $H = 1$ the process is the infinitely-many-neutral-alleles diffusion with stationary law $\mathrm{PD}(\theta)$; for $H = 2$ it is a diffusion on the Thoma simplex.

## Depends on

- [Blockwise skew-product representation of the Wright–Fisher diffusion](blockwise-skew-product-of-the-wright-fisher-diffusion.md)
- [Ranked masses of the stationary Fleming–Viot measure](../diffusion-theory/fleming-viot-processes/ranked-frequencies-are-poisson-dirichlet.md)

## Expansion

Ranking makes the finite-$K$ processes exchangeable within marks, and the limit of the $K$-type Wright–Fisher diffusion with mutation $\theta_h/K$ per type is, after ranking, the Ethier–Kurtz infinitely-many-neutral-alleles diffusion. Since the skew-product representation holds for every $K$ and the random clocks depend only on the finite-dimensional mark process, the limit inherits the same structure. Stationarity is checked by showing $\int \mathbb A f\, d\mu^* = 0$ on a core, which follows from stationarity of $\mathrm{Dir}_H$ for $W$ and of $\mathrm{PD}(\theta_h)$ for each time-changed component.

## Sources

- C. Costantini, M. Ruggiero, "Multiple Poisson-Dirichlet diffusions on generalized Kingman simplices", arXiv:2602.20266 (2026), Theorems 3.2, 3.3, 3.6, 3.7, 4.1 and 4.3, Corollaries 3.4 and 4.2, <https://doi.org/10.48550/arXiv.2602.20266>.
