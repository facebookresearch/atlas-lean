# Breadth-first-search distances from the source do not decrease along Edmonds–Karp

If, after one step of the [Edmonds–Karp algorithm](edmonds-karp.md), breadth-first search from $s$ in the new residual graph reports distance $d'$ for a vertex $u$, then breadth-first search from $s$ in the old residual graph reports a distance $d \le d'$ for $u$ (in particular, $u$ was already reachable). This is inequality (1) of Edmonds and Karp's Proposition 3, stated with the distances the algorithm computes.

## Informally uses

- [One Edmonds–Karp step does not shorten distances from the source (Proposition 3 (1))](walk-step-source.md): the walk form of the statement.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 2 and 3, Lemmas 1 and 2, Theorem 1).
