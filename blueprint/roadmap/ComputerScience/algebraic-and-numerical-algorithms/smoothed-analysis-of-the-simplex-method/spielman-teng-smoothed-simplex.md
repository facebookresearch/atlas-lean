# Spielman-Teng polynomial smoothed complexity of a shadow vertex simplex method

There is a two-phase shadow vertex simplex method whose smoothed complexity on linear programs with $d$ variables and $n$ constraints is bounded by a polynomial in $n$, $d$ and $1/\sigma$; the original analysis bounds the expected number of pivots by $\widetilde{O}(d^{55} n^{86} \sigma^{-30} + d^{70} n^{86})$. Thus, although standard pivot rules take exponentially many steps in the worst case, every linear program becomes polynomially solvable by the simplex method after a Gaussian perturbation of its data of standard deviation $\sigma$.

## Proof sketch

Phase I constructs an auxiliary program with a known starting vertex whose shadow path leads to a feasible vertex of the smoothed program, and Phase II runs the shadow vertex rule on a plane spanned by the objective and a direction optimized by the starting vertex. The core estimate bounds the expected shadow size polynomially: by the polar section picture, it suffices to show that edges of the section are unlikely to be short, which follows from bounding the probability that the angle between consecutive optimizing directions or the distance of a vertex to a facet boundary is small (the distance and angle lemmas), using anti-concentration of Gaussian perturbations.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)
- [Smoothed complexity](../../sorting-and-searching/algorithm-analysis-models/smoothed-complexity.md)

## Proof depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- D. A. Spielman, S.-H. Teng, "Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time", Journal of the ACM 51 (2004), arXiv:cs/0111050.
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667.
