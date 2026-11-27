# Slack truncation preserves the stationary law of complex-balanced networks

**Setting.** Let $(\mathcal{S}, \mathcal{C}, \mathcal{R}, \Lambda)$ be a stochastic mass-action reaction network whose deterministic mass-action model has a complex-balanced steady state $c^* \in \mathbb{R}_{>0}^d$, and let $(\widetilde{\mathcal{S}}, \widetilde{\mathcal{C}}, \widetilde{\mathcal{R}}, \Lambda^N)$ be a regular slack network with slack reactants $Y_1, \dots, Y_m$, built as in [the convergence of slack-network truncations](convergence-of-slack-network-truncations.md) by appending rows $D = U - WC$ with each row of $U$ constant. Let $X$ and $X_N$ be the associated processes started at the same $\vec x_0$, with stationary distributions $\pi$ and $\pi_N$, and let $\mathbb{S}_N$ be the state space of $X_N$.

**Lemma.** The deterministic mass-action model of the slack network has the complex-balanced steady state $\tilde c = (c^*, 1, \dots, 1)^\top$.

**Theorem.** There is a constant $M_N > 0$ such that

$$\pi_N(\vec x) = M_N\,\pi(\vec x), \qquad \vec x \in \mathbb{S}_N.$$

In particular, by the Anderson–Craciun–Kurtz theorem, $\pi_N$ is the product-form Poisson law $\prod_i e^{-c_i^*}(c_i^*)^{x_i}/x_i!$ restricted and renormalized to $\mathbb{S}_N$.

## Depends on

- [Convergence of slack-network truncations of the chemical master equation](convergence-of-slack-network-truncations.md)
- [Anderson–Craciun–Kurtz on a finite class](../../stochastic-mass-action-metabolic-control-and-flu/poisson-weight-vec-mul-class-generator.md)

## Proof sketch

For complex balance one needs, for every complex $\eta$, that mass-action flux into $\eta$ equals flux out of $\eta$ at the steady state. Setting each slack concentration to $1$ leaves every monomial $\tilde c^{\tilde\nu}$ equal to $(c^*)^{\nu}$, because the slack coordinates contribute factors $1^{D_{ij}} = 1$; so complex balance of $c^*$ transfers to $\tilde c$. Stochastically, complex balance of the slack network makes the restricted product-form measure satisfy the stationary master equation on each closed communication class of $\mathbb{S}_N$; the boundary indicator only removes transitions that would leave $\mathbb{S}_N$, and complex balancing holds class by class. Hence the slack stationary law is the original one conditioned on $\mathbb{S}_N$, and $M_N = 1/\pi(\mathbb{S}_N) \to 1$.

## Sources

- Jinsu Kim, Jason Dark, German Enciso and Suzanne Sindi, "Slack reactants: A state-space truncation framework to estimate quantitative behavior of the chemical master equation", *The Journal of Chemical Physics* 153 (2020), 054117, <https://doi.org/10.1063/5.0013457>. Preprint version: arXiv:2005.05503 (2020), Lemma 6.1 and Theorem 6.2 (Section 6) with proofs in the final appendix, <https://doi.org/10.48550/arXiv.2005.05503>.
