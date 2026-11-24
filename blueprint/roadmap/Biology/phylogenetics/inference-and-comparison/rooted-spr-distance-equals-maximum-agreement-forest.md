# Rooted SPR distance equals the maximum agreement forest number

Let $T$ and $T'$ be rooted binary phylogenetic $X$-trees, each with its root regarded as a vertex $\rho$ at the end of a pendant edge adjoined to the original root, and with $\rho$ included in the label set. An agreement forest for $T$ and $T'$ is a collection of trees with label sets $L_\rho, L_1, \dots, L_k$ that partition $X \cup \{\rho\}$ with $\rho \in L_\rho$, such that each component is isomorphic to both $T|L_i$ and $T'|L_i$, and the subtrees $T(L_i)$ are vertex-disjoint in $T$, as are the $T'(L_i)$ in $T'$; $m(T, T')$ is the minimum possible $k$, the number of components minus one. Bordewich and Semple (2005, Theorem 2.1) prove $d_{\mathrm{rSPR}}(T, T') = m(T, T')$, where $d_{\mathrm{rSPR}}$ is the rooted subtree prune and regraft distance. From this they deduce that computing $d_{\mathrm{rSPR}}$ is NP-hard (Theorem 1.1) and that the decision problem parameterized by the distance is fixed-parameter tractable (Theorem 3.4): repeated subtree and chain reductions (Rules 1 and 2*) give trees with at most $28d$ leaves at the same distance $d$, so the question $d_{\mathrm{rSPR}} \le k$ is decided in time $O((56k)^{2k}p(|X|))$ for a polynomial $p$.

## Expansion

1. Definitions: rooted binary phylogenetic trees, rooted subtree prune and regraft (rSPR) operations, and agreement forests with the root convention; the difference from the earlier definition in which $\rho$ is not a label (Figures 2 and 3).
2. $m(T, T') \le d_{\mathrm{rSPR}}(T, T')$, by induction on the distance.
3. $d_{\mathrm{rSPR}}(T, T') \le m(T, T')$, by realizing an agreement forest with $m$ rSPR moves.
4. Theorem 1.1: NP-hardness by reduction, including the history of the earlier flawed proof.
5. Theorem 3.4: the reduction rules, the bound $28d$ on the reduced leaf set (Lemma 3.3), and the resulting fixed-parameter algorithm.

## Sources

- M. Bordewich and C. Semple, On the computational complexity of the rooted subtree prune and regraft distance, Ann. Comb. 8 (2005), 409–423, Theorems 1.1, 2.1 and 3.4. <https://doi.org/10.1007/s00026-004-0229-z>
