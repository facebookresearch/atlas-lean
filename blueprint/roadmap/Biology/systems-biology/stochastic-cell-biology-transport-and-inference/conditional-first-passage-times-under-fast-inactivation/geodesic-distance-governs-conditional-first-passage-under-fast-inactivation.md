# Geodesic distance governs conditional first passage under fast inactivation

Let $X(t)$ be a diffusive searcher in $\mathbb{R}^d$ (or on a compact connected Riemannian manifold, possibly with reflecting obstacles) with characteristic diffusivity $D > 0$, and let $\tau = \inf\{t > 0 : X(t) \in U_{\mathrm T}\}$ be its first passage time to a target $U_{\mathrm T}$ that is the closure of its interior. Assume the initial distribution has compact support $U_0$ disjoint from the target. In each of the following settings the short-time condition $\lim_{t\to 0^+} t\ln\mathbb{P}(\tau\le t) = -C$ holds with

$$ C = \frac{L^2}{4D} , $$

where $L$ is the appropriate distance from $U_0$ to $U_{\mathrm T}$:

- pure diffusion in $\mathbb{R}^d$: $L$ is the Euclidean distance;
- the Itô diffusion $dX = b(X)\,dt + \sqrt{2D}\,\Sigma(X)\,dW$ with bounded Hölder drift and uniformly elliptic Hölder $a = \Sigma\Sigma^{\top}$: $L$ is the geodesic distance in the Riemannian metric $a^{-1}$, independent of $b$;
- diffusion on a manifold with reflecting obstacles: $L$ is the length of the shortest admissible path avoiding the obstacles;
- a partially absorbing target with finite reactivity $\kappa > 0$: $C$ is unchanged.

Combined with the conditional-moment asymptotics, for an independent gamma inactivation time $\sigma$ with rate $\lambda$ and every $m \ge 1$

$$ \mathbb{E}\big[\tau^m \,\big|\, \tau < \sigma\big] \sim \Big(\frac{L}{2\sqrt{D\lambda}}\Big)^m \quad \text{as } \lambda \to \infty . $$

Searchers that succeed under fast inactivation travel along shortest paths, avoid slow-diffusion regions and obstacles, and are unaffected by drift and by finite target reactivity.

## Depends on

- [Conditional moments of a first passage time under fast gamma inactivation](conditional-moments-of-a-first-passage-time-under-fast-gamma-inactivation.md)

## Expansion

The value of $C$ comes from Varadhan's formula (and Norris's extension to manifolds), $\lim_{t\to0}t\ln p(t,x,y) = -d(x,y)^2/(4D)$, applied to hitting probabilities as in the theory of fastest first passage times. For a partially absorbing half-line target the explicit survival function involves $\mathrm{erfc}(L/\sqrt{4Dt})$ and an extra Robin term, and both share the same logarithmic short-time limit $-L^2/(4D)$. In particular this confirms the earlier conjecture that the conditional mean first passage time of a strongly inactivated signal scales like the shortest distance divided by $2\sqrt{D\lambda}$. If searchers can start arbitrarily close to the target, the condition fails and the scaling changes.

## Sources

- Sean D. Lawley, "The Effects of Fast Inactivation on Conditional First Passage Times of Mortal Diffusive Searchers", SIAM Journal on Applied Mathematics 81 (2021), 1–24, <https://doi.org/10.1137/20m1324818>. Published version of arXiv:2003.05515, cited next; locators there refer to the arXiv version.
- S. D. Lawley, "The effects of fast inactivation on conditional first passage times of mortal diffusive searchers", arXiv:2003.05515 (2020), Section 4 (examples: simple diffusion, space-dependent drift and diffusivity, manifolds with reflecting obstacles, partially absorbing targets) and Section 5.1 (confirmation of the strong-inactivation conjecture). <https://doi.org/10.48550/arXiv.2003.05515>
