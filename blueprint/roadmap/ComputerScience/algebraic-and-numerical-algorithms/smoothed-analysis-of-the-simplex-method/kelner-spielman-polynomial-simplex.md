# Kelner-Spielman randomized polynomial-time simplex algorithm

There is a randomized simplex algorithm that solves every linear program $\max\{c^\top x : Ax \le b\}$ with rational data of total encoding length $L$ in expected time polynomial in $n$, $d$ and $L$; it was the first randomized polynomial-time simplex algorithm for linear programming. Its running time is weakly polynomial, depending on $L$, so it does not resolve whether linear programming admits a strongly polynomial algorithm.

## Proof sketch

The program is reduced to a related program whose boundedness and optimal vertex determine the original answer, and the right-hand sides of that program are randomly perturbed while the constraint matrix is kept fixed. The key estimate bounds the expected shadow size under right-hand side perturbations in terms of quantities controlled by $L$, again through an edge-length argument on a two-dimensional section, so the shadow vertex rule takes polynomially many steps; perturbations of magnitude $2^{-\mathrm{poly}(L)}$ preserve the optimal basis, which yields an exact optimum.

## Depends on


## Proof depends on

- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)
- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- J. A. Kelner, D. A. Spielman, "A Randomized Polynomial-Time Simplex Algorithm for Linear Programming", STOC (2006).
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667.
