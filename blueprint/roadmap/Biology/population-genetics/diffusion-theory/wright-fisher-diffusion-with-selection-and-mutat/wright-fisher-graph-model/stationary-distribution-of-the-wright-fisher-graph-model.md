# Stationary distribution of the Wright–Fisher graph model

**Model.** Allelic types at a locus are the vertices $\mathcal V$ of a connected directed graph $\mathcal G = (\mathcal V, \mathcal E)$. A population of size $N$ is either monomorphic at a vertex $u$ (state $(u,u,0)$) or biallelic on an edge $\langle u,v\rangle$, with derived allele $v$ at frequency $y \in (0,1)$ (state $(u,v,y)$). From a monomorphic state $u$ a new mutant $v$ arises at rate proportional to $\lambda_{uv}$ (non-recurrent mutation, initial frequency $1/N$); while polymorphic, the frequency follows the Wright–Fisher diffusion with scaled directional selection coefficient $\gamma_{uv}$, generator $\tfrac12 y(1-y)\partial_y^2 + \gamma_{uv}y(1-y)\partial_y$, until it is absorbed at $u$ or $v$. Selection is directional and antisymmetric, $\gamma_{vu} = -\gamma_{uv}$. Fixation from frequency $1/N$ has probability $q_\gamma(1/N) = \omega_\gamma/N + O(N^{-2})$ with

$$\omega_\gamma = \frac{2\gamma}{1 - e^{-2\gamma}} \ (\gamma \ne 0), \qquad \omega_0 = 1,$$

Mutation rates satisfy $\lambda_{uv} > 0 \iff \lambda_{vu} > 0$, every vertex has positive total mutation rate, and the graph is irreducible. With entry frequency $x = 1/N$, the embedded boundary chain (polymorphic excursions collapsed to jumps) moves $u \to v$ at rate proportional to $h_{uv} = \lambda_{uv}\,q_{\gamma_{uv}}(1/N)$, and its large-$N$ scaling has rates $\lambda_{uv}\omega_{\gamma_{uv}}$.

**Reversibility assumption.** Antisymmetry of $\gamma$ and positive rates in both directions do **not** by themselves make the boundary chain reversible: on a neutral triangle with clockwise mutation rates $2$ and reverse rates $1$, multiplying the three balance equations gives $8 = 1$. Assume therefore that both boundary rate families satisfy detailed balance, equivalently Kolmogorov's cycle condition $\prod_{i} h_{u_iu_{i+1}} = \prod_{i} h_{u_{i+1}u_i}$ around every cycle $u_0 \to u_1 \to \dots \to u_n = u_0$ of $\mathcal G$, and likewise for $\lambda_{uv}\omega_{\gamma_{uv}}$ (both hold automatically when $\mathcal G$ is a tree). **Departure from the source.** This reversibility assumption is **not** in the source; it is added here to close a gap in its Section 2.3. The source assumes only conditions i)–iii) above (positive total rates, $\lambda_{uv} > 0 \iff \lambda_{vu} > 0$, irreducibility) and antisymmetric selection, and then asserts that the invariant boundary measure "must satisfy" the edge-wise balance $\eta^x_u\lambda_{uv}q_{\gamma_{uv}}(x) = \eta^x_v\lambda_{vu}(1 - q_{\gamma_{uv}}(1-x))$, its Eq. (6), concluding that there is "a unique invariant and reversible measure" on the boundary; its Eq. (14) in Section 3.1 does the same for the scaled rates. Those identities give edge-wise balance only once the chain is known to be reversible, and the neutral-triangle example shows it need not be. Theorem 1, Proposition 1 and the corollaries below are therefore stated under the cycle condition, which holds automatically on trees; without it the source's argument does not establish them.

Let $(\eta^{1/N}_u)$ and $(\eta_u)$ be the probability vectors with $\eta^{1/N}_u h_{uv} = \eta^{1/N}_v h_{vu}$ and $\eta_u\lambda_{uv}\omega_{\gamma_{uv}} = \eta_v\lambda_{vu}\omega_{\gamma_{vu}}$ on every edge.

**Theorem.** Under the reversibility assumption, the process has an edge-reversible stationary distribution $\mu$, with boundary weights proportional to $\eta^{1/N}$, and for large $N$, $\mu = \mu_N + O(1/N)$ where the monomorphic probabilities are $\mu_N(u,u,0) = \eta_u/\Omega'_N$ and the polymorphic density on edge $\langle u,v\rangle$ is

$$\mu_N(u,v,y)\,dy = \frac{2\eta_u\lambda_{uv}}{\Omega'_N}\Big\{\frac{\omega_{\gamma_{uv}}\big(1 - e^{-2\gamma_{uv}(1-y)}\big)}{2\gamma_{uv}\,y(1-y)}\,\mathbf 1_{\{1/N<y<1\}} + (N - \omega_{\gamma_{uv}})\,\mathbf 1_{\{0<y<1/N\}}\Big\}dy,$$

with normalization $\Omega'_N = \Omega_N + O(\ln N/N)$,

$$\Omega_N = 1 + 2\sum_{u,v}\eta_u\lambda_{uv}\big(1 + \ln N + K_{\gamma_{uv}}\big), \qquad K_\gamma = \omega_\gamma\int_0^1(-\ln y)\big(e^{-2\gamma y} - e^{-2\gamma(1-y)}\big)dy.$$

In the neutral case ($\gamma \equiv 0$) the polymorphic density reduces to the familiar $1/y$ site-frequency profile.

**Consequence for diversity.** Extended to $L$ loci with mutation parameters $\theta_{uv} = \lambda_{uv}L$, the effective mutation rate $\hat\theta_{\mathrm{eff}}$ satisfies $\theta_{\min}/(1 + 2L^{-1}(1+\ln N)\theta_{\min}) \le \hat\theta_{\mathrm{eff}} \le \hat\theta \le \theta_{\max}$. Let $X^j_\infty$ be the stationary state of locus $j = 1,\dots,L$ and $\mathcal X_\infty = \sum_{j=1}^L \delta_{X^j_\infty}$ the point measure collecting them, so $\langle\mathcal X_\infty, f\rangle = \sum_j f(X^j_\infty)$. Let $f \ge 0$ depend only on the frequency, $f(u,v,y) = f(y)$, with $f(0) = 0$ (monomorphic states contribute nothing) and a limit $f(0+) = \lim_{y\downarrow0} f(y)$. For homogeneous mutation $\theta$ the expected frequency spectrum then obeys $E_N\langle\mathcal X_\infty, f\rangle \le 2\theta\{f(0+) + \int_{1/N}^1 f(y)/y\,dy\}$: directional selection never increases genetic variation beyond its neutral level.

## Depends on

- [Backward generator of the Wright–Fisher diffusion with selection](../../wright-fisher-diffusion/generator.md)
- [Kimura's fixation probability](../../wright-fisher-diffusion/kimura-fixation.md)

## Proof depends on

- [Green function, occupation times and mean exit times of a one-dimensional diffusion](../../selection-duality-and-general-one-dimensional-di/green-function-occupation-times-and-mean-exit-ti.md)

## Expansion

The process alternates between boundary sojourns and edge excursions. The embedded boundary chain jumps $u \to v$ at rate $\lambda_{uv}q_{\gamma_{uv}}(x)$ for entry level $x$, and the antisymmetry of $\gamma$ gives the symmetry $\omega_{\gamma_{vu}} = e^{-2\gamma_{uv}}\omega_{\gamma_{uv}}$ (and $q_{\gamma_{vu}}(x) = 1 - q_{\gamma_{uv}}(1-x)$), which is the edge-wise ingredient of detailed balance; together with the cycle condition it makes the boundary chain reversible with law $\eta^{1/N}$, approximated by $\eta$ for large $N$. On each edge, the occupation density of an excursion entering at $x$ is the Green function $G(x, dy)$ of the selected Wright–Fisher diffusion killed at $0$ and $1$; stationarity weights excursions by $\eta_u\lambda_{uv}$, giving $\mu \propto \eta$ on vertices and $\propto \sum \eta_u G(\nu^x_{uv}, dy)$ on edges. Taking $x = 1/N$ and expanding the Green function produces the closed form above, the $\ln N$ in $\Omega_N$ coming from the $1/y$ singularity near the entry point.

## Sources

- Ingemar Kaj, Carina F. Mugal and Rebekka Müller-Widmann, "A Wright–Fisher graph model and the impact of directional selection on genetic variation", *Theoretical Population Biology* 159 (2024), 13–24, <https://doi.org/10.1016/j.tpb.2024.07.004>. Numbering as in the preprint arXiv:2302.07542v1, <https://arxiv.org/abs/2302.07542v1>: Section 2.1 (mutation-rate conditions i)–iii)), Section 2.3 (boundary chain and the detailed-balance claim (6)), Section 3.1 (scaled detailed balance (14); the reversibility assumption here closes the gap in both), Theorem 1 (edge-reversible stationary measure), Proposition 1 (large-$N$ approximation), Corollary 1 (edge sums), Theorem 2 and Corollary 2 (multi-locus bounds).
