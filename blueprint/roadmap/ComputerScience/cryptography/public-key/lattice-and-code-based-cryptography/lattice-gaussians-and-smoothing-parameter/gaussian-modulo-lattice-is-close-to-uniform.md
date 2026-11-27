# A Gaussian reduced modulo a lattice is close to uniform

Let $L$ be a full-rank lattice, $s > 0$, $c$ any center, and let $D_{s,c}$ be the continuous Gaussian with density proportional to $\rho_{s,c}$. The total variation distance between $D_{s,c} \bmod L$ (on the torus $E/L$) and the uniform distribution on $E/L$ is at most $\tfrac12\rho_{1/s}(L^* \setminus\{0\})$. In particular, if $s \ge \eta_\varepsilon(L)$ the distance is at most $\varepsilon/2$.

## Proof sketch

By Poisson summation the density of $D_{s,c} \bmod L$ relative to the uniform density is $\sum_{y \in L^*}\rho_{1/s}(y)e^{2\pi i\langle y, x - c\rangle}$; the deviation from $1$ is bounded pointwise by $\rho_{1/s}(L^* \setminus \{0\})$.

## Depends on

- [Smoothing parameter of a lattice](smoothing-parameter.md)
- [Total variation distance between finite measures](../../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
- O. Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM 56(6), 2009.
