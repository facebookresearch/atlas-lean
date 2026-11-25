# Breadth-first-search distances to the sink do not decrease along Edmonds–Karp

Distances to $t$ are computed, as in the algorithm, by breadth-first search from $t$ in the transposed residual graph. If, after one step of the [Edmonds–Karp algorithm](edmonds-karp.md), the reported distance from $u$ to $t$ is $d'$, then before the step it was some $d \le d'$. This is inequality (2) of Edmonds and Karp's Proposition 3.

## Informally uses

- [One Edmonds–Karp step does not shorten distances to the sink (Proposition 3 (2))](walk-step-sink.md): the walk form of the statement.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 2 and 3, Lemmas 1 and 2, Theorem 1).
