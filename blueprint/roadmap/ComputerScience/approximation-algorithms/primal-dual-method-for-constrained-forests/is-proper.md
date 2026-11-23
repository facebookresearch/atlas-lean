# Proper requirement function

A function $f : 2^V \to \{0, 1\}$ is proper when

1. (symmetry) $f(S) = f(V \setminus S)$ for every $S$, and
2. (disjointness) if $A$ and $B$ are disjoint and $f(A) = f(B) = 0$, then $f(A \cup B) = 0$.

The constrained forest problem asks for a minimum-cost edge set meeting $\delta(S)$ whenever
$f(S) = 1$. Goemans and Williamson also assume $f(V) = 0$, which the
[integrality-gap theorem](exists-forest-cost-le-of-lp-feasible.md) takes as a separate hypothesis.

## Sources

- M. X. Goemans and D. P. Williamson, "A general approximation technique for constrained forest problems", *SIAM J. Comput.* 24(2) (1995), 296–317 (journal version), §1, p. 296–297.
