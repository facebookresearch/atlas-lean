# Reinhardt-Allender double counting

For a digraph $G$ with source $s$ and $k \ge 0$, let $R_k$ be the set of vertices at distance at most $k$ from $s$, $c_k = |R_k|$ and $\Sigma_k = \sum_{v \in R_k} d(s, v)$. Given the exact values $c_k$ and $\Sigma_k$, a **double-counting transcript** for round $k$ scans the vertices in a fixed order and, for each vertex, either skips it or supplies a walk from $s$ of at most $k$ edges ending at it; the transcript **passes** if the number of supplied vertices equals $c_k$ and the sum of the supplied walk lengths equals $\Sigma_k$, which forces every supplied walk to be a shortest walk. The next round's counts are computed from successful transcripts by scanning successors of $R_k$.

## Depends on

- [The complexity class NL](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md)
- [Immerman-Szelepcsenyi theorem: NL = coNL](../../../../TheoryOfComputation/complexity-classes/immerman-szelepcsenyi.md)

## Sources

- K. Reinhardt and E. Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
