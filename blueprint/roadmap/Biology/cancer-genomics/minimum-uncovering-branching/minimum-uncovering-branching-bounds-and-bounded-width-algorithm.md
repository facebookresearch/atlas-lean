# Minimum uncovering branching: antichain bounds and polynomial time for bounded width

**Setting.** A binary matrix $M \in \{0,1\}^{m\times n}$ records which of $m$ tumor samples (rows) carry which of $n$ somatic mutations (columns). The support of column $c$ is the set of rows with a $1$ in $c$. The *containment digraph* $D_M$ has the distinct supports as vertices and an arc $u \to v$ whenever $u \subsetneq v$; it is the strict poset $P_M$ of supports under inclusion, and $\operatorname{wd}(M)$ is its width (largest antichain). A *branching* $B$ of $D_M$ is a set of arcs with at most one outgoing arc per vertex (each non-maximal support is assigned to at most one superset). A row $r \in v$ is *uncovered in $v$* if no $u$ with $(u,v) \in B$ contains $r$; $U(B)$ is the set of uncovered pairs $(r,v)$. The *uncovering number* is $\beta(M) = \min_B |U(B)|$ (Minimum Uncovering Branching, MUB), and $\beta_\ell(M)$ is the minimum over *linear* branchings (at most one incoming arc per vertex as well), which correspond bijectively to chain partitions of $D_M$. MUB is equivalent to Minimum Conflict-free Row Split: the minimum number of extra rows needed to split samples into clones so that the matrix becomes a perfect phylogeny matrix.

**Lower bounds.** Let $D_{M,r}$ be the subposet of supports containing row $r$, $W(M) = \sum_{r} \operatorname{wd}(D_{M,r})$, and $\alpha_w(M)$ the maximum of $\sum_{v \in X}|v|$ over antichains $X$ of $D_M$. Then

$$\alpha_w(M) \;\le\; W(M) \;\le\; \beta(M) \;\le\; \beta_\ell(M),$$

and $\alpha_w(M)$ is computable in time $O(\lvert A(D_M)\rvert^{1+o(1)})$ by a maximum-weight antichain algorithm.

**Theorem (maximal elements).** If $P_M$ has exactly $q = \operatorname{wd}(M)$ maximal elements, then $\alpha_w(M) = W(M) = \beta(M) = \beta_\ell(M)$, and an optimal branching can be computed in time $O(n^2(m + n^{o(1)}))$.

**Theorem (bounded width).** $\beta(M)$ can be computed in time

$$O\!\left(n^{\operatorname{wd}(D_M)(\operatorname{wd}(D_M)+1)}\big(\operatorname{wd}(D_M)^4 + n^{2+o(1)}\big) + n^2 m\right),$$

so MUB is polynomial for every fixed width (whereas it is APX-complete already for bounded height).

## Depends on

- [Perfect phylogeny for a binary character matrix](../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/is-perfect-phylogeny.md)

## Expansion

Every row $r$ must be uncovered at least once on each chain of any chain cover of $D_{M,r}$ that a branching induces, and by Dilworth's theorem $D_{M,r}$ needs $\operatorname{wd}(D_{M,r})$ chains; this is the Hajirasouliha–Raphael bound $\beta(M) \ge \sum_r \chi(G_{M,r})$ rewritten with a perfect conflict graph whose chromatic number equals that width. Any antichain $X$ forces each $v \in X$ to contribute $|v|$ distinct uncovered rows across the per-row posets, giving $\alpha_w \le W$. When the number of maximal elements equals the width, an optimal chain partition can be aligned with the maximal elements and computed by bipartite maximum matching, closing all inequalities. For bounded width, optimal branchings have a structure that can be guessed among $n^{O(\operatorname{wd}^2)}$ candidate configurations, each completed by matchings and antichain computations.

## Sources

- N. Baghirova, E. Galby and M. Milanič, "Perfect phylogenies via the Minimum Uncovering Branching problem: efficiently solvable cases", *IEEE Transactions on Computational Biology and Bioinformatics* 22(5) (2025), 2043–2056, Theorems 2.1, 3.1, 4.2, 4.8 and Corollaries 3.3, 3.5, <https://doi.org/10.1109/tcbbio.2025.3580476> (preprint arXiv:2506.18578).
- I. Hajirasouliha and B. J. Raphael, "Reconstructing mutational history in multiply sampled tumors using perfect phylogeny mixtures", WABI 2014, LNCS 8701, <https://doi.org/10.1007/978-3-662-44753-6_27>.
