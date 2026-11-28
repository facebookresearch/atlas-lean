# wDCJ distance formula and its complexity

A weighted genome on a set $V$ of $2n$ gene extremities is a perfect matching on $V$ whose edges (intergenes) carry nonnegative integer weights (intergene sizes). A wDCJ cuts two edges $ab$, $cd$ of weights $w(ab)$, $w(cd)$ and reconnects them as $ac$, $bd$ (or $ad$, $bc$), splitting the total weight $w(ab) + w(cd)$ between the two new edges at the cut positions. Two genomes $g_1, g_2$ on $V$ are evenly weighted if their total weights agree. In the breakpoint graph $BG(g_1, g_2)$, the union of the two matchings, every component is an alternating cycle; the imbalance of a cycle $C$ is $I(C) = w_1(C) - w_2(C)$, the difference of the total $g_1$- and $g_2$-weights on $C$, and $C$ is balanced if $I(C) = 0$. Let $c$ be the number of cycles, $n_b$ and $n_u$ the numbers of balanced and unbalanced cycles.

(1) If all cycles of $BG(g_1, g_2)$ are balanced, $wDCJ(g_1, g_2) = n - n_b = n - c$, as for the unweighted DCJ distance.

(2) In general,

$$wDCJ(g_1, g_2) = n - c + 2m,$$

where $m$ is the minimum number of cycle merges needed to turn the unbalanced cycles into balanced ones; equivalently, $c - m$ is attained by partitioning the multiset of imbalances of the unbalanced cycles into the maximum number of zero-sum parts.

(3) Deciding the wDCJ distance is strongly NP-complete (by reduction from 3-Partition).

(4) It is $\frac{4}{3}$-approximable, by merging zero-sum pairs, then (approximately) zero-sum triples, then all remaining unbalanced cycles.

(5) It is fixed-parameter tractable in $n_u$: solvable in $O^*(3^{n_u})$ time by a Held–Karp-type dynamic programme over subsets of unbalanced cycles.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

A wDCJ changes the number of cycles by $+1$ (split), $-1$ (merge) or $0$, so $wDCJ \ge n - c$. In a balanced cycle of length at least $4$ there are consecutive edges $e, f, g$ with $e, g \in g_1$ and $w(e) + w(g) \ge w(f)$, which allows a split into two balanced cycles; hence only balanced splits are needed when all cycles are balanced. An unbalanced cycle can never become trivial, and splits cannot repair imbalance, so imbalances must first be cancelled by merges. Optimal scenarios use no cycle freezes, perform merges before splits and never merge a balanced cycle, giving $m$ merges followed by $n - (c - m)$ splits. The minimum $m$ is a maximum zero-sum set partition problem, which encodes 3-Partition.

## Sources

- G. Fertin, G. Jean and E. Tannier, "Algorithms for computing the double cut and join distance on both gene order and intergenic sizes", *Algorithms for Molecular Biology* 12 (2017), Statement of the problem, Lemma 1, Propositions 2–6, Theorem 7, Theorem 8, Theorem 11 and Theorem 12. <https://doi.org/10.1186/s13015-017-0107-y> (PMC5460591)
