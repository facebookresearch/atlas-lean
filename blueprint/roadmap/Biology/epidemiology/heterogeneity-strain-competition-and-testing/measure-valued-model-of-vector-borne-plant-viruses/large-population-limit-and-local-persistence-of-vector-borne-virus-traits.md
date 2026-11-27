# Large-population limit and local persistence of vector-borne virus traits

**Model.** Host plants sit at the points of a finite set $E$; insect vectors move in a bounded domain $D \subset \mathbb{R}^d$ by reflected diffusion; viruses carry a trait $z$ in a compact set $\mathcal{X}$. The state is a triple of point measures: $\nu_v$ on $E\times\mathcal{X}$ (viruses on plants), $\nu_u$ on $D$ (vectors not carrying virus) and $\nu_c$ on $D \times \mathcal{X}$ (vectors carrying a virus of trait $z$). A virus of trait $z$ on plant $x$ reproduces at rate $b(x,z)$, its offspring mutating with probability $\mu$ to a trait drawn from a kernel $m(z,\cdot)$; it dies at rate $d(z) + c\,\langle \nu_v^x, 1\rangle$ (logistic competition with the virus load of plant $x$); it is acquired by a free vector at $y$ at rate $\beta(y, x, \langle\nu_v^x,1\rangle, z)$; and a carrying vector at $y$ deposits its virus on plant $x$ at rate $\eta(y,x,z)$. Throughout (Assumption 1 of the source), the diffusion coefficients are Lipschitz with positive diffusivity, $m$ is a probability density, the competition parameter satisfies $c > 0$, the rates $b$, $d$, $\beta$ and $\eta$ (and the death rate of viruses on vectors) are bounded, and $\beta$ is Lipschitz in the virus-load argument. In the $K$-th model, with $\lambda \in (0,1]$, viruses carry weight $1/K$ and vectors weight $K^{-\lambda}$, vector motion is accelerated by $K^{1-\lambda}$, and the rates scale as $c_K = c/K$, $\beta_K = K^{-\lambda}\beta$ and $\eta_K = K^{1-\lambda}\eta$ (Assumption 2).

**Theorem (extinction of the stochastic model).** If $\mathbb{E}\langle \nu_v(0),1\rangle < \infty$, then under Assumption 1 the total virus population of the individual-based process goes extinct almost surely.

**Theorem (large-population limit, $\lambda = 1$).** Let vectors move by reflected Brownian motion, and let the initial masses have finite third moments and converge to deterministic limits that are absolutely continuous (with respect to counting measure on $E$ and Lebesgue measure). Then $\nu^{(K)} \to \xi$ in law, where $\xi$ has densities $(g_v, g_u, g_c)$ forming the unique solution of

$$\partial_t g_v = (1-\mu)b\,g_v + \mu\!\int_{\mathcal{X}}\! b(x,z')m(z',z)g_v(z')\,dz' - \Big[d(z) + c\!\int_{\mathcal{X}}\! g_v\,dz'\Big]g_v - \Big[\int_D \beta\big(y,x,\textstyle\int g_v,z\big) g_u(y)\,dy\Big] g_v + \int_D \eta(y,x,z)\,g_c(y,z)\,dy,$$

$$\partial_t g_u = \Delta g_u - \Big[\sum_{x\in E}\int_{\mathcal{X}} \beta\big(y,x,\textstyle\int g_v,z\big)g_v(x,z)\,dz\Big]g_u + \sum_{x\in E}\int_{\mathcal{X}} \eta(y,x,z)\,g_c(y,z)\,dz,$$

$$\partial_t g_c = \Delta_y g_c + \Big[\sum_{x\in E}\beta\big(y,x,\textstyle\int g_v,z\big)g_v(x,z)\Big]g_u - \Big[\sum_{x\in E}\eta(y,x,z)\Big]g_c,$$

with Neumann boundary conditions on $\partial D$. For $\lambda \in (0,1)$ the vectors homogenize and the virus density satisfies a closed integro-differential equation with averaged acquisition and deposition rates.

**Proposition (local persistence).** Let $R(x,z) = (1-\mu)b(x,z) - d(z) - \int_D \beta(y,x,z)\,dy$. If $g_v(0,x,z) > 0$ and $R(x,z) > 0$, then $\liminf_{t\to\infty} g_v(t,x,z) > 0$: trait $z$ persists on plant $x$ in the deterministic limit.

## Expansion

Almost-sure extinction of the finite stochastic system comes from logistic competition: the virus load on each plant is dominated by a subcritical-at-high-density birth–death process, and with finitely many plants and bounded rates the absorbing state is reached with probability one, so persistence is a large-$K$ (quasi-stationary) phenomenon. The limit follows from martingale problems for the rescaled measure-valued process, tightness via moment bounds on the total mass, and uniqueness for the limiting system; when $\lambda<1$ the vectors move on a faster time scale and Kurtz's averaging theorem replaces their configuration by its equilibrium. The persistence criterion compares the per-capita growth of trait $z$ at low density, $(1-\mu)b - d$, with the maximal loss rate to vectors.

## Sources

- Mario Ayala, Jerome Coville and Raphael Forien, "A measure-valued stochastic model for vector-borne viruses", Latin American Journal of Probability and Mathematical Statistics 21 (2024), 1145, <https://doi.org/10.30757/alea.v21-45>; numbering as in arXiv:2211.04563: Theorems 1.3–1.6 and Proposition 1.7 (Section 1); Theorems 3.1–3.3.
