# Vershynin's smoothed simplex walks of length polylogarithmic in the number of constraints

For every linear program with $d > 3$ variables and $n > d$ constraints, there is a two-phase shadow vertex simplex method with a randomized Phase I (adding an artificial random vertex) whose expected number of pivot steps on the smoothed program is

$$
O\!\left(\log^2 n \cdot \log\log n \cdot \left(d^3 \sigma^{-4} + d^5 \log^2 n + d^9 \log^4 d\right)\right),
$$

polylogarithmic in the number $n$ of constraints. Vershynin's remark after the theorem leaves open whether the factor $\log^2 n \cdot \log\log n$ can be removed.

The planar-section estimate used in the proof is separate from this solver bound: if $a_1, \dots, a_n \in \mathbb{R}^d$ are independent Gaussian vectors with centers of norm at most $1$ and standard deviation $\sigma \le 1/(6\sqrt{d \log n})$, and $E$ is a fixed plane, then $\mathbb{E}\,|\mathrm{edges}(\mathrm{conv}(a_1, \dots, a_n) \cap E)| \le C d^3 \sigma^{-4}$ for an absolute constant $C$. Scaling larger noise down to $\sigma = 1/(6\sqrt{d\log n})$ gives the polar-section shadow size bound $S_{\mathrm{e}}(n, d, \sigma) = O(d^3 \sigma^{-4} + d^5 \log^2 n)$ for all $\sigma > 0$. In particular random perturbations create short edge paths between vertices, so the $n - d$ Hirsch-type length is no obstruction for smoothed programs.

## Proof sketch

Instead of finding a feasible vertex of the smoothed program, Phase I adds $d$ random constraints so that a vertex optimal for a random objective appears, and with constant probability this does not change the optimum, so a constant expected number of independent trials suffices; this statistically decouples the starting point of the walk from the smoothed data. The pivot count then reduces in a black-box manner to the expected size of planar sections of random polytopes (the polar section bound), which is bounded by an improved version of the edge-length estimates. The solver makes one shadow vertex call on an interpolation program and on average four calls on unit programs, and a stopping-time argument combines the section bounds for these calls into the stated estimate.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Proof depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)
- [Spielman-Teng polynomial smoothed complexity of a shadow vertex simplex method](spielman-teng-smoothed-simplex.md)

## Sources

- R. Vershynin, "Beyond Hirsch Conjecture: Walks on Random Polytopes and Smoothed Complexity of the Simplex Method", SIAM Journal on Computing 39 (2009), arXiv:cs/0604055, Theorems 1.2, 6.1 (with the remark after it) and 6.2, and condition (6.1).
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667, Section 1.1 and Table 1.
