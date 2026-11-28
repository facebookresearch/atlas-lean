# Fickian release from a slab into a perfect sink

A dissolved drug initially uniform in a slab of thickness $2\ell$ and released by constant-coefficient diffusion into a perfect sink leaves with fraction $1 - \tfrac{8}{\pi^2}\sum_{k\ge0} (2k+1)^{-2}e^{-(2k+1)^2\pi^2Dt/(4\ell^2)}$.

Let $\ell > 0$, $D > 0$ and constants $c_1 \ne c_0$. Let $c(x,t)$ be the solution (classical for $t > 0$, attaining the initial value in $L^2(0, 2\ell)$) of $c_t = D c_{xx}$ on $0 < x < 2\ell$, $t > 0$, with $c(x,0) = c_1$ for $0 < x < 2\ell$ and $c(0,t) = c(2\ell,t) = c_0$ for $t > 0$. Then, with the series converging uniformly on $[0,2\ell]\times[t_0,\infty)$ for every $t_0 > 0$,

$$\frac{c - c_0}{c_1 - c_0} = \frac{4}{\pi}\sum_{k=0}^{\infty}\frac{1}{2k+1}\sin\frac{(2k+1)\pi x}{2\ell}\,\exp\left(-\frac{(2k+1)^2\pi^2 D t}{4\ell^2}\right).$$

If $c_1 > c_0$ (in particular the sink case $c_0 = 0$, $c_1 > 0$), let $M_t$ be the amount released per unit area by time $t$ and $M_\infty = 2\ell(c_1 - c_0)$ the initially releasable amount; then

$$\frac{M_t}{M_\infty} = 1 - \frac{8}{\pi^2}\sum_{k=0}^{\infty}\frac{1}{(2k+1)^2}\exp\left(-\frac{(2k+1)^2\pi^2 D t}{4\ell^2}\right).$$

## Context

Undergraduate applied mathematics: the exact solution behind "Fickian" release from non-swelling, non-eroding films and gels. The same series describes uptake of solvent by a sheet (the source's Eq. (39)). The open copy's rendering of Eq. (17) omits $D$ in the exponent; it is restored here from the dimensional diffusion equation and Eq. (39). As $t \to 0^+$, $M_t/M_\infty = \tfrac{2}{\ell}\sqrt{Dt/\pi}$ up to exponentially small corrections, an asymptotic statement, not an exact power law on any interval.

## Depends on

None.

## Proof depends on

- [Single-mode solution of the Dirichlet heat equation](../../../../Analysis/partial-differential-equations/heat-equation/single-mode-solution-of-the-dirichlet-heat-equation.md)
- [Weak solutions of the one-dimensional heat equation](../../../../Analysis/partial-differential-equations/weak-solutions-of-parabolic-equations/weak-solutions-of-the-one-dimensional-heat-equation.md)

## Expansion

Each term is a rescaled single Dirichlet mode; the sine coefficients of the constant $c_1 - c_0$ on $(0, 2\ell)$ are $4(c_1 - c_0)/((2k+1)\pi)$ for odd modes; uniform convergence for $t \ge t_0 > 0$ and uniqueness of the weak solution identify the series with the solution. Integrating over $x$ and using $\sum_k (2k+1)^{-2} = \pi^2/8$ gives $M_t/M_\infty$. The short-time asymptotic needs a separate lemma (Poisson summation or the image solution).

## Sources

- C. Mircioiu, V. Voicu, V. Anuta, A. Tudose, C. Celia, D. Paolino, M. Fresta, R. Sandulovici and I. Mircioiu, "Mathematical Modeling of Release Kinetics from Supramolecular Drug Delivery Systems", Pharmaceutics 11(3), 140 (2019), <https://doi.org/10.3390/pharmaceutics11030140>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6471682/>: Section 2.1 (Fick's second law), Section 2.5.1 Eqs. (16)–(17) and the derivation in Appendix A, the sink condition discussion after Eq. (17), and Section 3.2.2 Eq. (39) for the cumulative fraction
