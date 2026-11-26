# Pair coalescence time tail and Malécot analogue for planar logistic branching random walks

**Model (logistic branching random walk, LBRW).** Let $p = (p_{y-x})$ be a symmetric, aperiodic, irreducible random-walk kernel on $\mathbb{Z}^2$ with finite range, $\lambda = (\lambda_{y-x})$ a non-negative symmetric competition kernel of finite range, and $m\in(1,3)$. Given the generation-$n$ configuration $\eta_n \in \mathbb{N}_0^{\mathbb{Z}^2}$, each particle at $x$ has $\mathrm{Poisson}\bigl((m - \sum_z \lambda_{z-x}\eta_n(z))^+\bigr)$ offspring, which independently take one $p$-step; equivalently

$$\eta_{n+1}(x) \sim \mathrm{Poisson}\Bigl(\sum_y p_{yx}\, \eta_n(y)\bigl(m - \textstyle\sum_z\lambda_{z-y}\eta_n(z)\bigr)^+\Bigr)$$

independently over $x$. For $0 < \lambda_0 \ll 1$ and $\lambda_z \ll \lambda_0$ ($z\ne0$) the process survives with positive probability and, given survival, converges to a unique non-trivial equilibrium; the restriction $m\in(1,3)$ makes the logistic map $u\mapsto u(m-\lambda u)^+$ have a stable positive fixed point $(m-1)/\lambda$, and local population sizes fluctuate randomly under this endogenous density regulation.

Sample one individual at the origin and one at $Nx$ ($x\in\mathbb{R}^2\setminus\{0\}$, rounded to $\mathbb{Z}^2$) from the stationary two-sided process, follow their ancestral lineages backward in time, and let $\tau_{\rm coal}$ be the number of generations back to their most recent common ancestor.

**Theorem.** Under the above assumptions on $m$ and $\lambda$,

$$\lim_{N\to\infty}\mathbb{P}_{Nx}\bigl(\tau_{\rm coal} > N^{2\gamma}\bigr) = \frac{1}{\gamma} \qquad \text{for every } \gamma \ge 1 .$$

**Corollary (Malécot analogue).** With infinite-alleles mutation at rate $\mu_N = c\,N^{-2\gamma}$ per generation, $c\in(0,\infty)$, $\gamma\ge1$, the probability of identity by descent of the two samples satisfies

$$\phi_N(Nx) = \mathbb{E}_{Nx}\bigl[(1-\mu_N)^{2\tau_{\rm coal}}\bigr] \longrightarrow 1 - \frac{1}{\gamma}.$$

This is exactly the limit of the Wright–Malécot formula $\phi(x)\approx K_0(\sqrt{2\mu}\,\lVert x\rVert/\sigma)/(2\pi\sigma^2\delta + K_0(\sqrt{2\mu}\,\kappa/\sigma))$ under the same scaling, since $K_0(z)\sim-\log z$ as $z\downarrow0$, and it agrees with the corresponding results for a suitably scaled two-dimensional stepping-stone model with fixed deme sizes.

## Depends on

- [Isolation by distance](../structured-coalescent/isolation-by-distance.md)

## Expansion

The two lineages are delayed coalescing random walks in a dynamic random environment, the time reversal of the occupation field $\eta$; averaged over $\eta$ they are not Markov. The proof uses a joint regeneration construction: at random regeneration times the future of the pair is (approximately) independent of the past, and between regenerations the pair's displacement has light tails, so on large scales the separation behaves like a two-dimensional random walk while the lineages are far apart. For planar random walk started at distance $N$, the probability of not having entered a ball of fixed radius by time $N^{2\gamma}$ is asymptotically $\log N/\log N^{\gamma} = 1/\gamma$ (logarithmic recurrence). Separation and sphere-hitting lemmas control what happens once the lineages are close (coalescence with probability bounded below before they drift apart again), so the tail of $\tau_{\rm coal}$ inherits the hitting-time tail. Integrating $(1-\mu_N)^{2t}\approx e^{-2cN^{-2\gamma}t}$ against this tail gives the corollary. The result justifies replacing locally fluctuating population sizes by fixed effective sizes in isolation-by-distance formulas on large spatial scales.

## Sources

- M. Birkner, A. Depperschmidt, T. Schlüter, *Pair coalescence times of ancestral lineages of two-dimensional logistic branching random walks*, arXiv:2405.02090 (2024), Section 1: Theorem 1.1 (survival and equilibrium, quoted from earlier work), Theorem 1.3, Corollary 1.4. <https://doi.org/10.48550/arXiv.2405.02090>
