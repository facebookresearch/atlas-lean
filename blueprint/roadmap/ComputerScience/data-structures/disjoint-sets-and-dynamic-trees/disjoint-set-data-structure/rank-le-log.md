# Ranks are at most $\lfloor \log_2 n \rfloor$

In every union-find structure with $n$ nodes obtained from the empty one by make-set, find with
path compression and union by rank, every node has rank at most $\lfloor \log_2 n \rfloor$; an
index that is not a node has rank $0$, and $\lfloor \log_2 0 \rfloor$ is read as $0$.

For a root this follows from the [rank lemma](two-pow-rank-le-class-size.md), since a class has
at most $n$ nodes; a non-root node has smaller rank than its root.

## Informally uses

- [Rank lemma for linking by rank (roots)](two-pow-rank-le-class-size.md): $2^{\mathrm{rank}(r)}
  \le n$ for every root $r$.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §2, consequence of Lemma 2 (compare Corollary 1).
