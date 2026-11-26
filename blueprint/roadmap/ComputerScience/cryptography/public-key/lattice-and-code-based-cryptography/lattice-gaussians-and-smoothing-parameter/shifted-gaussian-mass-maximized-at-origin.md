# Shifted lattice Gaussian mass is maximized at the origin

For every discrete subgroup $L$ of a finite-dimensional real inner-product space, every $s > 0$ and every center $c$, $\rho_{s,c}(L) \le \rho_{s}(L)$. No full-rank hypothesis is needed.

## Proof sketch

Project $c$ onto the span of $L$, which only scales all terms by a common factor at most one. On the span, Poisson summation writes $\rho_{s,c}(L)$ as $\det(L^*) s^n \sum_{y \in L^*}\rho_{1/s}(y) e^{2\pi i\langle c, y\rangle}$, whose terms have nonnegative coefficients, so the sum is maximized at $c = 0$.

## Depends on

- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](discrete-gaussian-on-a-lattice.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
