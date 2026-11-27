# Tutte's matrix theorem and Lovász's randomized matching test

$\det T_G \ne 0$ as a polynomial if and only if $G$ has a perfect matching. Hence substituting independent uniform values from a finite set $S$ gives a randomized test with one-sided error: it never reports a matching when none exists, and misses an existing perfect matching with probability at most $n/|S|$.

## Proof sketch

Permutations with an odd cycle cancel in pairs by reversing the cycle; the remaining permutations, all of whose cycles are even, contribute squares of matching monomials (the determinant is the square of the Pfaffian), which cannot cancel. The error bound is Schwartz-Zippel.

## Depends on

- [The Tutte matrix of a graph](tutte-matrix.md)

## Sources

- W. T. Tutte, "The Factorization of Linear Graphs", Journal of the London Mathematical Society 22, 1947.
- L. Lovász, "On Determinants, Matchings, and Random Algorithms", Fundamentals of Computation Theory (FCT 1979), Akademie-Verlag, 1979.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
