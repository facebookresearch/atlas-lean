# Rank lemma for linking by rank (roots)

Let $U$ be a union-find structure obtained from the empty one by make-set, find with path
compression and union by rank. For every root $r$ of $U$,

$$2^{\mathrm{rank}(r)} \le |\{\, i : \mathrm{root}(i) = r \,\}|,$$

the right-hand side being the number of nodes in the class of $r$.

This is Tarjan and van Leeuwen's Lemma 2 (linking by rank: $\mathrm{size}(x) \ge
2^{\mathrm{rank}(x)}$) for the roots, whose trees are their classes. Path compression changes
neither ranks nor classes; a link of two roots of equal rank $k$ creates a root of rank $k + 1$
whose class has at least $2^k + 2^k$ nodes, and a link of unequal ranks keeps the larger rank.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §2, Lemma 1 (linking by size) and Lemma 2 (linking by rank).
