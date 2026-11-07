# Maderna–Venturelli theorem on hyperbolic motions

Let $E$ be a finite-dimensional real
inner product space of dimension at least $2$, let $N$ be a natural number, and let
$m = (m_1, \dots, m_N)$ be positive masses. Let $x_0 \in E^N$, let $a \in E^N$ be a configuration
without collisions with $\lVert a \rVert_m = 1$, where
$\lVert a \rVert_m = \bigl(\sum_i m_i \lVert a_i \rVert^2\bigr)^{1/2}$, and let $h > 0$. Then
there are a solution $x : \mathbb{R} \to E^N$ of the $N$-body problem with masses $m$ and a
function $\varepsilon : \mathbb{R} \to E^N$ with $\lVert \varepsilon(t) \rVert / t \to 0$ as
$t \to \infty$ such that $x(0) = x_0$, the configuration $x(t)$ is without collisions for every
$t > 0$, and $x(t) = \sqrt{2h}\, t\, a + \varepsilon(t)$ for every $t \ge 0$.

## Sources

- E. Maderna and A. Venturelli, `Viscosity solutions and hyperbolic motions: a new PDE method for the N-body problem`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_viscosity_solutions` of the lean-eval benchmark.
