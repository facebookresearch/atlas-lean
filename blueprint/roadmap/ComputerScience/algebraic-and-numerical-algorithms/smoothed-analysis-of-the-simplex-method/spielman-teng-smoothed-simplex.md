# Spielman-Teng polynomial smoothed complexity of a shadow vertex simplex method

There is a two-phase shadow vertex simplex method whose smoothed complexity on linear programs with $d$ variables and $n$ constraints is bounded by a polynomial in $n$, $d$ and $1/\sigma$: for every base program, the expected number of pivots on its Gaussian perturbation of standard deviation $\sigma$ is polynomial, and the original analysis bounds it by $\widetilde{O}(d^{55} n^{86} \sigma^{-30} + d^{70} n^{86})$. The bound is on the expectation over the perturbation; it does not bound the number of pivots of every realised walk. Thus, although standard pivot rules take exponentially many steps in the worst case, every linear program is solved by this simplex method in expected polynomially many pivots after such a perturbation.

## Proof sketch

The first phase replaces the right-hand side $b$ by an artificial, "somewhat uniform" right-hand side $b'$, constructed so that a randomly chosen basis of $A$ yields a vertex of $Ax \le b'$; from that vertex the shadow vertex rule computes a maximizer of the objective for the right-hand side $b'$. The second phase interpolates the right-hand side from $b'$ to $b$ and follows the optimal basis along this interpolation to an optimal solution for $b$. Neither program is exactly a smoothed unit program and the shadow planes depend on the data, which makes this reduction the delicate part of the analysis. The core estimate bounds the expected shadow size polynomially: by the polar section picture, it suffices to show that edges of the section are unlikely to be short, which follows from bounding the probability that the angle between consecutive optimizing directions or the distance of a vertex to a facet boundary is small (the distance and angle lemmas), using anti-concentration of Gaussian perturbations.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)
- [Smoothed complexity](../../sorting-and-searching/algorithm-analysis-models/smoothed-complexity.md)

## Proof depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- D. A. Spielman, S.-H. Teng, "Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time", Journal of the ACM 51 (2004), arXiv:cs/0111050.
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667, Section 1.1.
