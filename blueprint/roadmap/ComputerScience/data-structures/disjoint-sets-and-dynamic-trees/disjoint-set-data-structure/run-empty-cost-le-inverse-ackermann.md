# Tarjan–van Leeuwen bound for union by rank with path compression

There is a constant $C$ such that every sequence of set-union operations with $n \ge 1$
make-sets and $m$ finds (a union counting as two finds), run from the empty union-find structure
with linking by rank and path compression, has total [cost](step.md) at most

$$C\,\bigl(n + m\,\alpha(m + n, n)\bigr),$$

where $\alpha$ is the [inverse Ackermann function of Tarjan and van Leeuwen](inverse-ackermann-tv-l.md).
By their Remark 2, $\alpha(m, n) \le 3$ for $n < 2^{16}$ and, for all practical purposes,
$\alpha$ is a constant no larger than four; by their Theorem 2 of §1, no separable algorithm
does better than $\Omega(n + m\,\alpha(m + n, n))$.

The proof uses the multiple partition technique of Tarjan (1975), which Tarjan and van Leeuwen
extend: the ranks are partitioned into blocks at several levels, coarser at higher levels, and
the nodes on each find path are charged level by level according to how compaction moves their
parents' ranks between blocks (their §3, Lemmas 4–6).

## Background

- [Cost bound $O(n + m \log n)$ from the empty structure](run-empty-cost-le-log.md): the weaker
  bound.
- [Rank lemma for linking by rank (roots)](two-pow-rank-le-class-size.md): the rank property on
  which the analysis rests.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §3, Theorem 3; §1, Theorem 2 (lower bound) and Remarks 1–2.
- R. E. Tarjan, *Efficiency of a good but not linear set union algorithm*, J. ACM 22(2) (1975)
  215–225, the source of the multiple partition technique, as Tarjan and van Leeuwen state in §3.
