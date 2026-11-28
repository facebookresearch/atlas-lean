# Kelner-Spielman randomized polynomial-time simplex algorithm

There is a randomized simplex algorithm that solves every linear program $\max\{c^\top x : Ax \le b\}$ with rational data of total encoding length $L$ in time polynomial in $n$, $d$ and $L$ with high probability; it was the first randomized polynomial-time simplex algorithm for linear programming. Its running time is weakly polynomial, depending on $L$, so it does not resolve whether linear programming admits a strongly polynomial algorithm.

## Proof sketch

Solving the program is reduced to finding a point satisfying the primal constraints, the dual constraints and equality of the two objective values; by standard techniques, and after the Megiddo–Chandrasekaran perturbation that makes the system nondegenerate, this feasibility question becomes the question whether an auxiliary system $A_1 w \le b_1$, which is nonempty, is bounded. Boundedness of a nonempty polyhedron does not depend on its right-hand side, so the algorithm certifies boundedness or unboundedness of $A_1 w \le b_1'$ for a randomly perturbed right-hand side $b_1'$ while keeping $A_1$ fixed, and that certificate answers the question for the original system; no optimal basis has to survive the perturbation. The key estimate bounds the expected shadow size under right-hand side perturbations of a polytope in near-isotropic position, again through an edge-length argument on a two-dimensional section; the algorithm adds constraints creating an artificial starting vertex and, when a round fails, uses the failure to adjust the distributions and repeats, and the number of rounds, hence of steps, is polynomial in $n$, $d$ and $L$ with high probability.

## Proof depends on

- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)
- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- J. A. Kelner, D. A. Spielman, "A Randomized Polynomial-Time Simplex Algorithm for Linear Programming", STOC (2006), Sections 1, 5 and 6 (Theorem 6.3).
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667.
