# Distances between rankings: Kendall tau and Spearman footrule

This node collects distances between rankings.

## Expansion

A sound expansion has separate pages for:

1. **Permutations.** On permutations of $n$ items, the Kendall tau distance $K$ (number of discordant pairs)
   and the Spearman footrule $F$ (sum of absolute rank differences) are metrics and satisfy
   $K \le F \le 2K$ (Diaconis–Graham). For rearrangements of a list without duplicates, $K$ is the
   [number of inversions](../../online-algorithms/list-update-problem/inv.md), which satisfies the
   [triangle inequality](../../online-algorithms/list-update-problem/inv-triangle.md).
2. **Top-$k$ lists.** The extensions of Fagin, Kumar and Sivakumar, each with its penalty parameter (for
   example the parameter $p$ of $K^{(p)}$ for pairs whose order one list does not determine): which of them are
   metrics (the footrule $F^{(\ell)}$ with location parameter $\ell > k$) and which are only near-metrics
   (every $K^{(p)}$ with $0 \le p \le 1$, and $F_{\min}$: on the top-2 lists $(1, 2)$, $(1, 3)$ and $(3, 4)$,
   $K^{(p)}$ takes the values $1$, $2$ and $4 + 2p$, which violate the triangle inequality), and the equivalence
   class of measures within constant multiples of each other, with the constants stated per measure.

## Sources

- Comparing Top k Lists (Fagin, Kumar, Sivakumar), SIAM J. Discrete Math 2003, course copy — SIAM J. Discrete Mathematics 17(1) 2003, Section 3 (definitions of $K^{(p)}$ and $F^{(\ell)}$, Proposition 3.8 and the counterexample after it, p. 146), Definition 4.5, inequality (17) credited to Diaconis and Graham, Theorem 5.1, Corollary 5.2 and Theorem 5.3. <https://www.biz.uiowa.edu/faculty/nstreet/Fagin03.pdf>
