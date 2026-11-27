# Time-changed neutral diffusion under deterministic population-size change: construction and fixation

Let $\nu : [0, \infty) \to (0, \infty)$ be continuous, the relative population size at time $t$, let $\Lambda(t) = \int_0^t \nu(s)^{-1}\, ds$, and let $Y$ be the [continuous neutral Wright–Fisher process](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md) started at $x \in [0, 1]$. Then $X = Y \circ \Lambda$ solves the [time-inhomogeneous martingale problem](time-inhomogeneous-martingale-problem.md) for $\nu(t)^{-1} L_0$, by the [deterministic clock change](deterministic-clock-change-for-martingale-proble.md). For this solution:

- if $\Lambda(\infty) = \infty$, then $X$ is absorbed at $0$ or $1$ almost surely and is [fixed with probability $x$](../absorption-of-the-neutral-wright-fisher-martinga/measure-real-fixation-eq.md);
- if $\Lambda(\infty) < \infty$, then $X_t \to X_\infty = Y_{\Lambda(\infty)}$, and the probability of absorption is $\mathbb P_x(\tau_Y \le \Lambda(\infty)) < 1$ for $x \in (0, 1)$, where $\tau_Y$ is the absorption time of $Y$.

For $\nu \equiv 1$, $X = Y$. For $\nu(t) = e^t$, $\Lambda(\infty) = 1$, and for $x \in (0, 1)$ the probability of eventual fixation is $\mathbb P_x(Y_1 = 1) < x$.

## Depends on

- [Time-inhomogeneous martingale problem](time-inhomogeneous-martingale-problem.md)
- [Deterministic clock change for martingale problems](deterministic-clock-change-for-martingale-proble.md)
- [Continuous modification selected by Kolmogorov's theorem](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md)
- [A neutral solution started at x is fixed with probability x](../absorption-of-the-neutral-wright-fisher-martinga/measure-real-fixation-eq.md)

## Expansion

A full proof page must still establish:

- the two cases of the fixation statement, including $\mathbb P_x(\tau_Y > t) > 0$ for every finite $t$ and $x \in (0, 1)$;
- the exponential-growth example, using $\mathbb E\, Y_1 = x$ and $\mathbb P_x(0 < Y_1 < 1) > 0$;
- the explicit case of a piecewise-constant $\nu$ (a bottleneck).

## Sources

- S. P. Otto and M. C. Whitlock, "The probability of fixation in populations of changing size", *Genetics* 146(2) (1997), 723–733, <https://doi.org/10.1093/genetics/146.2.723>, also at <https://pmc.ncbi.nlm.nih.gov/articles/PMC1208011/> (background)
- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, "Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data", *PLoS Genetics* 5(10):e1000695, 2009, <https://journals.plos.org/plosgenetics/article?id=10.1371/journal.pgen.1000695> (background)
