# Stochastic persistence of a logistic reaction–diffusion SPDE

**Model.** Let $D \subset \mathbb{R}^N$ be open, connected and bounded with smooth boundary. Fix $d > 0$, $C^1$ functions $K, r, E \colon \overline D \to [0, \infty)$ with $K > 0$ (carrying capacity, growth rate, harvesting rate), a $C^1$ function $\sigma \colon [0,\infty) \to \mathbb{R}$ with $\sigma(0) = 0$ and locally Lipschitz, bounded derivative, a real Brownian motion $w_t$ and $\epsilon \in [0, 1]$. The population density $u_t \ge 0$ solves

$$du = \Big[d\,\Delta\Big(\frac{u}{K}\Big) + r u\Big(1 - \frac{u}{K}\Big) - E u\Big]dt + \epsilon\, \sigma(u)\, K\, dw_t \quad \text{on } D,$$

with Neumann condition $\partial_n (u/K) = 0$ on $\partial D$; it defines a Markov process on nonnegative continuous functions on $\overline D$.

**Theorem (small noise).** Let $\lambda$ be the principal eigenvalue of

$$d\,\Delta\Big(\frac{u}{K}\Big) + (r - E)\,u = \lambda u \ \text{ on } D, \qquad \partial_n(u/K) = 0.$$

If $\lambda > 0$, there is $\bar\epsilon > 0$ such that for all $\epsilon < \bar\epsilon$ the population is *stochastically persistent*:
1. for every $\delta > 0$ there are $0 < b < B < \infty$ such that for every nonnegative $u_0 \ne 0$, almost surely

$$\liminf_{T \to \infty} \frac{1}{T}\, \mathrm{Leb}\Big\{t \le T : b \le \int_D u_t \le B\Big\} \ge 1 - \delta;$$

2. there is an invariant measure $\mu_+$ with $\mu_+(\{0\}) = 0$.

**Theorem (any noise level).** For fixed $\epsilon > 0$, let $v_t = u_t / \|u_t\|_{L^1}$ for the linearization $du = [d\Delta(u/K) + (r - E)u]\,dt + \epsilon\sigma'(0) K u\, dw_t$, and let

$$\Lambda = \sup_{\mu} \mu\Big(-\int_D d\,\Delta(vK^{-1})K^{-1} + (r - E) v K^{-1} + \tfrac12 \epsilon^2 \sigma'(0)^2 \Big[\int_D v\Big]^2\Big)$$

over invariant measures $\mu$ of $v_t$ on $\{\|v\|_{L^1} = 1\}$. If $\Lambda < 0$, the same two conclusions hold.

## Depends on

- [Stochastic persistence of competitive Lotka–Volterra SPDEs via invasion rates](invasion-rate-criterion-for-stochastic-lotka-volterra-spdes.md)

## Expansion

Both results instantiate a general Lyapunov criterion for Feller processes on infinite-dimensional spaces: if a function $V$ that blows up at the extinction set has generator $H = \mathcal{L}V$ with $\sup_\mu \mu H < 0$ over invariant measures on the extinction boundary, then empirical occupation measures stay away from that boundary. Near $u = 0$ the dynamics is the linearization, and $V = -\ln \int_D u$ turns $\mu H$ into an average exponential growth rate. For $\epsilon \to 0$ that rate tends to the principal eigenvalue $\lambda$, which gives the small-noise statement by continuity of the criterion in parameters.

## Sources

- J. Foldes, D. Stacy, "Stochastic Persistence in Infinite Dimensions", arXiv:2601.19145 (2026), Theorem 24 (general criterion), Theorem 28 (robustness), Section 7.1: Theorem 111, Definition 115 and Theorem 117, <https://doi.org/10.48550/arXiv.2601.19145>.
