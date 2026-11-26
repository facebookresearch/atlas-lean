# Vershynin's smoothed simplex walks of length polylogarithmic in the number of constraints

There is a simplex method with a randomized Phase I (adding an artificial random vertex) that solves the smoothed program with an expected number of pivots

$$
O\!\left(\max\left(d^5 \log^2 n,\; d^9 \log^4 d,\; d^3 \sigma^{-4}\right)\right) ,
$$

polylogarithmic in the number $n$ of constraints. The corresponding shadow bound for smoothed unit programs is $S(n, d, \sigma) = O(d^3 \sigma^{-4} + d^5 \log^2 n)$. In particular random perturbations create short edge paths between vertices, so the $n - d$ Hirsch-type length is no obstruction for smoothed programs.

## Proof sketch

Instead of finding a feasible vertex of the smoothed program, Phase I adds $d$ random constraints so that a vertex optimal for a random objective appears, and with constant probability this does not change the optimum; this statistically decouples the starting point of the walk from the smoothed data. The pivot count then reduces in a black-box manner to the expected size of planar sections of random polytopes, which is bounded by an improved version of the edge-length estimates for the polar section.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Proof depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)
- [Spielman-Teng polynomial smoothed complexity of a shadow vertex simplex method](spielman-teng-smoothed-simplex.md)

## Sources

- R. Vershynin, "Beyond Hirsch Conjecture: Walks on Random Polytopes and Smoothed Complexity of the Simplex Method", SIAM Journal on Computing 39 (2009), arXiv:cs/0604055.
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667.
