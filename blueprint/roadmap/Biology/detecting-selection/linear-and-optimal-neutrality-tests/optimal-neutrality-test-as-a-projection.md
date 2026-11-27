# Optimal neutrality test as a projection

Let the neutral expected spectrum be $E_0(\xi_i) = \theta L\,\xi_i^0$ and an alternative scenario have expected spectrum $\theta L\,\bar\xi_i$. Let $c_{ij}^{-1}$ be the inverse of the covariance matrix $\operatorname{Cov}(\xi_i, \xi_j)$ and define the scalar product

$$\langle\langle \xi', \xi'' \rangle\rangle = \sum_{i,j} \xi'_i\,c_{ij}^{-1}\,\xi''_j .$$

Among centred, unit-variance linear tests $T_\Omega$, the one maximizing the expected value under the alternative is

$$T_O = \frac{\langle\langle \xi, \bar\xi\rangle\rangle - \langle\langle \xi, \xi^0\rangle\rangle\,\langle\langle \xi^0, \bar\xi\rangle\rangle / \langle\langle \xi^0, \xi^0\rangle\rangle}{\sqrt{\langle\langle \bar\xi, \bar\xi\rangle\rangle - \langle\langle \xi^0, \bar\xi\rangle\rangle^2 / \langle\langle \xi^0, \xi^0\rangle\rangle}},$$

whose value on the alternative mean spectrum is the maximum over all linear tests,

$$T_O^{(\max)} = \theta L\,\sqrt{\langle\langle \bar\xi, \bar\xi\rangle\rangle - \frac{\langle\langle \xi^0, \bar\xi\rangle\rangle^2}{\langle\langle \xi^0, \xi^0\rangle\rangle}} .$$

The numerator is the matrix element $\langle\langle \bar\xi, (1 - P_{\xi^0})\,\xi\rangle\rangle$ of the projection orthogonal to $\xi^0$, so $T_O$ vanishes on the neutral spectrum and is unchanged when any multiple of $\xi^0$ is added to $\bar\xi$: optimal tests depend only on the expected deviation from neutrality.

## Depends on

- [General linear neutrality tests and weight-consistent scaling](general-linear-neutrality-tests-and-weight-consistent-scaling.md)

## Expansion

Maximizing $E_1(T_\Omega)$ over weights is maximizing a linear functional divided by a quadratic norm, subject to the centring constraint. In the inner product defined by the inverse covariance, the Cauchy–Schwarz inequality makes the maximizer proportional to the component of $\bar\xi$ orthogonal to $\xi^0$, which yields the projection formula and its maximal value. Because the tests have mean $0$ and variance $1$ under the null, a larger mean under the alternative is a proxy for larger power; maximizing power directly leads to a related family of tunable tests.

## Sources

- S. E. Ramos-Onsins, G. Marmorini, G. Achaz and L. Ferretti, "A general framework for neutrality tests based on the site frequency spectrum", *Genes* 14 (2023), 1714, Section 2.3.2, Eqs. (32)–(35). <https://doi.org/10.3390/genes14091714> (PMC10531300)
