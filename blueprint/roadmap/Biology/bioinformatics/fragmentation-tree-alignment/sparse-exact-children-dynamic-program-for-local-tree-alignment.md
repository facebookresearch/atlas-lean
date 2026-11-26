# Sparse exact-children dynamic program for local tree alignment

In local alignment of unordered, arc-labeled trees $T_1, T_2$ (for example mass-spectrometry fragmentation trees), the table entries $S_{u,v}[A, B]$ of the standard subset dynamic program are monotone in $A$ and $B$: a positive entry forces all supersets to be positive, so tables fill up even when few node pairs align well. The **exact-children** reformulation stores instead

$$S'_{u,v}[A, B] = \text{best score of a local alignment of the subtrees at } u, v \text{ using exactly the children } A \subseteq C(u),\ B \subseteq C(v),$$

with $S'_{u,v}[A,B] = -\infty$ if no such alignment exists, $S'_{u,v}[\emptyset, \emptyset] = 0$, and $S(u,v) = \max_{A, B} S'_{u,v}[A, B]$. Auxiliary maxima $S'_{u,v}[*, B] = \max_{A} S'_{u,v}[A, B]$ and $S'_{u,v}[A, *]$ replace the full-subset lookups of the original recurrence.

**Pruning principle.** An entry with $S'_{u,v}[A, B] \le 0$ (other than $[\emptyset,\emptyset]$), or one **dominated** by an entry on subsets, $S'_{u,v}[A,B] \le S'_{u,v}[A', B']$ with $A' \subseteq A$, $B' \subseteq B$, $(A',B') \neq (A,B)$, can be discarded without changing the optimum.

**Complexity.** Evaluated by pushing scores from finalized entries (a Dijkstra-like successive approximation), the sparse program has the same worst case $O(3^{\Delta} 2^{\delta} \delta\, n_1 n_2)$ as the dense one; iterating only over stored positive entries $S'_{a,v}[*, B'] > 0$ in the deletion updates raises the worst case to $O(4^{\Delta} 2^{\delta} \delta\, n_1 n_2)$ with constant-time hash access, while remaining exact.

## Depends on

- [Degree-exponential dynamic program for unordered tree alignment](degree-exponential-dynamic-program-for-unordered-tree-alignment.md)

## Expansion

A non-positive partial alignment is never part of an optimal local alignment, because removing the children $A$, $B$ and everything below them gives score at least as large; a dominated entry can likewise be replaced by the dominating smaller one. With scoring schemes that penalize mismatching losses, most entries are non-positive or dominated, so storing the tables in hash maps (or lazily allocated arrays) cuts memory, and pushing updates only from positive finalized entries cuts running time. On real fragmentation-tree data this sparse variant was the fastest of the exact methods compared, including an integer linear program.

## Sources

- F. Hufsky, K. Dührkop, F. Rasche, M. Chimani, S. Böcker, "Fast alignment of fragmentation trees", Bioinformatics (2012), Section 2 (fragmentation trees, join operator, local alignment score), Section 3 (Eqs. 1-4, Lemma 1, Theorems 1 and 2), Section 4 (sparse dynamic programming, Eqs. 5-8). <https://doi.org/10.1093/bioinformatics/bts207> (PMC3371839)
