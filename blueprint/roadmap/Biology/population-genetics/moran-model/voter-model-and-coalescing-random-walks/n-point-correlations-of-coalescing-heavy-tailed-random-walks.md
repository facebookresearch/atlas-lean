# $N$-point correlations of coalescing heavy-tailed random walks

**Setting.** Start a coalescing random walk from every site of $\mathbb Z$: walkers jump at rate $1$ with a symmetric kernel in the domain of attraction of an $\alpha$-stable law, $\alpha \in (0, 1]$, so that the position $X_t$ of a single walker started at $0$ satisfies: $X_t/b_t$ converges to a stable law with density $g_\alpha$ for some scaling function $b_t$, and two walkers merge when they meet. These are the dual lineages of the voter model with long-range interactions. Let $\xi_t(x) = 1$ if site $x$ is occupied at time $t$, and fix the scaling function as $B_t := g_\alpha(0)/\mathbb P(X_t = 0)$ ((5) of the source; $B_t \sim b_t$), so that

$$l(t) = \int_0^t \frac{ds}{B_s} = \frac{1}{g_\alpha(0)}\int_0^t \mathbb P(X_s = 0)\,ds, \qquad \ell(t) = \frac{B_t\,l(t)}{t}.$$

The walk is marginally recurrent when $\alpha = 1$ and $l(\infty) = \infty$, and transient otherwise; in the marginally recurrent case assume $\ell(t)^K \ge l(t)$ for some $K$ and all large $t$.

**Theorem.**
1. *(Density.)* $\rho_1(t) = \mathbb P(\xi_t(0) = 1) = \dfrac{g_\alpha(0)\,l(2t)}{t}\bigl(1 + o(1)\bigr)$, with explicit error rates in each regime.
2. *(Non-collision.)* For $N$ independent walkers started at distinct $\mathbf x \in \mathbb Z^N$, the probability that no two have met by time $t$ is $\mathbb P(\tau_c > t) = \dfrac{c_{\mathbf x}}{l(2t)^{\binom N2}}\bigl(1 + o(1)\bigr)$.
3. *(N-point correlation.)* For distinct $x_1, \dots, x_N$,

$$\rho_N(\mathbf x, t) = \mathbb P\bigl(\xi_t(x_1) = \cdots = \xi_t(x_N) = 1\bigr) = \frac{c_{\mathbf x}\,g_\alpha(0)^N}{t^N\,l(2t)^{\binom N2 - N}}\bigl(1 + o(1)\bigr) \sim \rho_1(t)^N\,\mathbb P(\tau_c > t),$$

with error $O(l(t)^{-(1/(2K) - \varepsilon)})$ (marginally recurrent), $O(\ell(t)^{-(1/2 - \varepsilon)})$ (marginally transient, $\alpha = 1$) or $O(t^{-\eta})$ for any $\eta > 1/\alpha - 1$ ($\alpha < 1$). Moreover $\rho_N$ is negatively correlated: $\rho_N(\mathbf x, t) \le \rho_{N-1}(x_1, \dots, x_{N-1}, t)\,\rho_1(t)$.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

For $N$ occupied sites at time $t$, look backward: each site's occupant descends from a cluster of initial walkers, and the occupants must have avoided one another. Asymptotically the $N$ backward walks behave like independent walks conditioned not to collide, while the density of each surviving walker contributes $\rho_1(t)$; this gives the product $\rho_1^N \times \mathbb P(\tau_c > t)$. In the transient or weakly recurrent heavy-tailed regime each pair of walkers fails to meet with probability decaying like $1/l(2t)$ and the $\binom N2$ pairs become asymptotically independent, which produces the exponent. The heavy tails replace the Gaussian $t^{-1/2}$ decay of nearest-neighbour coalescence by slowly varying corrections.

## Sources

- Jinjiong Yu, "Sharp asymptotics for N-point correlation functions of coalescing heavy-tailed random walks", Stoch. Process. Appl. 195 (2026), 104897, <https://doi.org/10.1016/j.spa.2026.104897>. Numbering follows the arXiv version, arXiv:2505.05000 (2025): Theorems 1.1–1.3 and Theorem A.1, <https://doi.org/10.48550/arXiv.2505.05000>.
