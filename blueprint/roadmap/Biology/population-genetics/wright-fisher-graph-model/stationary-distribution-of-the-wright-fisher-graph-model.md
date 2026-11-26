# Stationary distribution of the Wright–Fisher graph model

**Model.** Allelic types at a locus are the vertices $\mathcal V$ of a connected directed graph $\mathcal G = (\mathcal V, \mathcal E)$. A population of size $N$ is either monomorphic at a vertex $u$ (state $(u,u,0)$) or biallelic on an edge $\langle u,v\rangle$, with derived allele $v$ at frequency $y \in (0,1)$ (state $(u,v,y)$). From a monomorphic state $u$ a new mutant $v$ arises at rate proportional to $\lambda_{uv}$ (non-recurrent mutation, initial frequency $1/N$); while polymorphic, the frequency follows the Wright–Fisher diffusion with scaled directional selection coefficient $\gamma_{uv}$, generator $\tfrac12 y(1-y)\partial_y^2 + \gamma_{uv}y(1-y)\partial_y$, until it is absorbed at $u$ or $v$. Selection is directional and antisymmetric, $\gamma_{vu} = -\gamma_{uv}$. Fixation from frequency $1/N$ has probability $q_\gamma(1/N) = \omega_\gamma/N + O(N^{-2})$ with

$$\omega_\gamma = \frac{2\gamma}{1 - e^{-2\gamma}} \ (\gamma \ne 0), \qquad \omega_0 = 1,$$

and the boundary weights $(\eta_u)_{u\in\mathcal V}$ are the unique probability vector satisfying the detailed balance relations $\eta_u\lambda_{uv}\omega_{\gamma_{uv}} = \eta_v\lambda_{vu}\omega_{\gamma_{vu}}$ on every edge.

**Theorem.** The process has an edge-reversible stationary distribution $\mu$, and for large $N$, $\mu = \mu_N + O(1/N)$ where the monomorphic probabilities are $\mu_N(u,u,0) = \eta_u/\Omega'_N$ and the polymorphic density on edge $\langle u,v\rangle$ is

$$\mu_N(u,v,y)\,dy = \frac{2\eta_u\lambda_{uv}}{\Omega'_N}\Big\{\frac{\omega_{\gamma_{uv}}\big(1 - e^{-2\gamma_{uv}(1-y)}\big)}{2\gamma_{uv}\,y(1-y)}\,\mathbf 1_{\{1/N<y<1\}} + (N - \omega_{\gamma_{uv}})\,\mathbf 1_{\{0<y<1/N\}}\Big\}dy,$$

with normalization $\Omega'_N = \Omega_N + O(\ln N/N)$,

$$\Omega_N = 1 + 2\sum_{u,v}\eta_u\lambda_{uv}\big(1 + \ln N + K_{\gamma_{uv}}\big), \qquad K_\gamma = \omega_\gamma\int_0^1(-\ln y)\big(e^{-2\gamma y} - e^{-2\gamma(1-y)}\big)dy.$$

In the neutral case ($\gamma \equiv 0$) the polymorphic density reduces to the familiar $1/y$ site-frequency profile.

**Consequence for diversity.** Extended to $L$ loci with mutation parameters $\theta_{uv} = \lambda_{uv}L$, the effective mutation rate $\hat\theta_{\mathrm{eff}}$ satisfies $\theta_{\min}/(1 + 2L^{-1}(1+\ln N)\theta_{\min}) \le \hat\theta_{\mathrm{eff}} \le \hat\theta \le \theta_{\max}$, and for homogeneous mutation $\theta$ the expected frequency spectrum obeys $E_N\langle\mathcal X_\infty, f\rangle \le 2\theta\{f(0+) + \int_{1/N}^1 f(y)/y\,dy\}$: directional selection never increases genetic variation beyond its neutral level.

## Expansion

The process alternates between boundary sojourns and edge excursions. The embedded boundary chain jumps $u \to v$ at rate $\lambda_{uv}q_{\gamma_{uv}}(x)$ for entry level $x$, and the antisymmetry of $\gamma$ gives the symmetry $\omega_{\gamma_{vu}} = e^{-2\gamma_{uv}}\omega_{\gamma_{uv}}$, so the boundary chain satisfies detailed balance and has the reversible law $\eta$. On each edge, the occupation density of an excursion entering at $x$ is the Green function $G(x, dy)$ of the selected Wright–Fisher diffusion killed at $0$ and $1$; stationarity weights excursions by $\eta_u\lambda_{uv}$, giving $\mu \propto \eta$ on vertices and $\propto \sum \eta_u G(\nu^x_{uv}, dy)$ on edges. Taking $x = 1/N$ and expanding the Green function produces the closed form above, the $\ln N$ in $\Omega_N$ coming from the $1/y$ singularity near the entry point.

## Sources

- Ingemar Kaj, Carina F. Mugal and Rebekka Müller, "A Wright-Fisher graph model and the impact of directional selection on genetic variation", arXiv:2302.07542 (2023), stationary measure theorem, large-$N$ approximation proposition, edge-sum corollary and multi-locus upper-bound theorem, <https://doi.org/10.48550/arXiv.2302.07542>.
