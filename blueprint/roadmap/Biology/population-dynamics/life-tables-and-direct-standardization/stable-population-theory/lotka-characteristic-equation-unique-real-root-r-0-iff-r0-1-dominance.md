# Lotka's characteristic equation

Let $\varphi \ge 0$ be the net maternity function, measurable on $[0, \infty)$ and not almost everywhere zero, and assume $f(s) = \int_0^\infty e^{-sa}\varphi(a)\, da$ is finite for every real $s$ (for example, $\varphi$ vanishes outside a reproductive interval $[\alpha, \beta]$). Then $f$ is continuous and strictly decreasing on $\mathbb{R}$, with $f(s) \to \infty$ as $s \to -\infty$ and $f(s) \to 0$ as $s \to \infty$, so the characteristic equation $f(r) = 1$ has exactly one real root $r$ (Feller 1941; Inaba 2017, Chapter 1). Since $f(0) = R_0 = \int_0^\infty \varphi$, the net reproduction ratio, $r > 0$, $r = 0$ or $r < 0$ according as $R_0 > 1$, $R_0 = 1$ or $R_0 < 1$. Writing $\varphi = R_0 g$ with $g$ a probability density, the characteristic equation is $R_0 \int e^{-ra} g(a)\, da = 1$, which is the [Euler–Lotka equation for the reproductive number](../../../epidemiology/euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff-reproduction-number.md) with $R = R_0$ and generation-interval law $g$; the statements above give the existence, uniqueness and sign of its real root, and the next sentence its dominance. Every complex root $z = u + iv$ with $v \ne 0$ satisfies $u < r$ (Feller 1941; Inaba 2017, Chapter 1): from $1 = \int e^{-ua}\cos(va)\varphi(a)\, da < \int e^{-ua}\varphi(a)\, da = f(u)$, where the inequality is strict because $\cos(va) < 1$ off the lattice $(2\pi/|v|)\mathbb{Z}$, which has measure zero, and $f$ is strictly decreasing.

## Depends on

- [Euler–Lotka equation for the reproductive number](../../../epidemiology/euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff-reproduction-number.md)

## Expansion

1. The Laplace transform of the net maternity function and its finiteness hypothesis.
2. Continuity, strict monotonicity and the limits of $f$ on the real line, by monotone and dominated convergence.
3. The unique real root and its sign in terms of $R_0$.
4. Strict dominance of $r$ over the real parts of the complex roots; the discrete-age (lattice) case, where dominance can fail for periodic fertility schedules, as a separate statement.

## Sources

- Original result: A. J. Lotka, Relation between birth rates and death rates, Science 26 (1907), 21–22. <https://doi.org/10.1126/science.26.653.21.b>
- W. Feller, On the integral equation of renewal theory, Ann. Math. Statist. 12 (1941), 243–267.
- H. Inaba, *Age-Structured Population Dynamics in Demography and Epidemiology*, Springer, 2017, Chapter 1. <https://doi.org/10.1007/978-981-10-0188-8>
