# The fractional stable matching polytope

For a one-to-one market with complete strict preferences on $n + n$ agents, the **fractional stable matching polytope** is the set of real $n \times n$ matrices $x \ge 0$ with all row and column sums equal to $1$ such that for every pair $(p, r)$,

$$
x_{pr} + \sum_{r' \succ_p r} x_{pr'} + \sum_{p' \succ_r p} x_{p'r} \ge 1 .
$$

The incidence matrix of a matching lies in it if and only if the matching is stable.

## Depends on

- [Stable matching](../stable-marriage-problem/is-stable-matching.md)
- [Perfect matching polytope](../matching-polytope/perfect-matching-polytope.md)

## Sources

- J. H. Vande Vate, "Linear Programming Brings Marital Bliss", Operations Research Letters 8(3), 1989.
- U. G. Rothblum, "Characterization of Stable Matchings as Extreme Points of a Polytope", Mathematical Programming 54, 1992.
