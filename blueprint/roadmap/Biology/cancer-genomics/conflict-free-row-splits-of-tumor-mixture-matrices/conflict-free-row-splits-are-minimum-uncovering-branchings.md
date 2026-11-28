# Conflict-free row splits are minimum uncovering branchings

**Setting.** Rows of a binary matrix $M\in\{0,1\}^{m\times n}$ are tumor samples and columns are mutations; a sample may be a mixture of several clones. Two columns are *in conflict* if some three rows restricted to them read $(1,1)$, $(1,0)$, $(0,1)$; a conflict-free matrix is exactly one whose columns form a perfect phylogeny (laminar supports). A *row split* of $M$ replaces each row $r_i$ by a set $R_i$ of binary rows whose bitwise OR is $r_i$. The *minimum conflict-free row split* (MCRS) problem asks for $\gamma(M)$, the least number of rows in a conflict-free row split, and its distinct-rows variant (MDCRS) asks for $\eta(M)$, the least number of distinct rows.

The *containment digraph* $D_M$ has as vertices the distinct column supports $\mathrm{supp}(c)\subseteq\{r_1,\dots,r_m\}$, with an arc $(v,v')$ whenever $v\subsetneq v'$. A *branching* $B\subseteq A(D_M)$ is a set of arcs with at most one arc leaving each vertex. A pair $(r,v)$ with $r\in v$ is *$B$-uncovered* if $r$ is in no in-neighbour of $v$ in $B$; let $U(B)$ be the set of uncovered pairs, and $I(B)$ the set of *$B$-irreducible* vertices, those with at least one uncovered element. Let $\beta(M)=\min_B|U(B)|$ and $\zeta(M)=\min_B|I(B)|$.

**Theorem.** Let $M$ have exactly $k$ distinct columns.

1. Every branching $B$ of $D_M$ yields, in time $O(kmn)$, a conflict-free row split of $M$ with exactly $|U(B)|$ rows and exactly $|I(B)|$ distinct rows.
2. Every conflict-free row split $M'\in\{0,1\}^{m'\times n}$ of $M$ yields, in time $O(mn+m'k^2+k^\omega)$, a branching $B$ with $|U(B)|$ at most the number of rows of $M'$ and $|I(B)|$ at most the number of distinct rows of $M'$.

Consequently

$$\gamma(M)=\beta(M)\qquad\text{and}\qquad\eta(M)=\zeta(M).$$

## Expansion

From a branching, build the *$B$-split*: one row for each uncovered pair $(r,v)$, with a $1$ in column $j$ exactly when the support of column $j$ is reachable from $v$ along $B$. Because each vertex has at most one outgoing arc, the reachable sets along $B$ form nested chains, so the column supports of the split are laminar and the split is conflict-free; the OR of the rows coming from $r$ recovers $r$ since every vertex containing $r$ is reached from some vertex where $r$ is uncovered. Conversely, in a conflict-free split the laminar family of column supports defines a forest on the supports of $M$, which induces a branching of $D_M$ whose uncovered pairs inject into rows of the split. The reformulation turns a matrix problem into a combinatorial optimization on a DAG, which drives the later min-max and approximability results.

## Sources

- Ademir Hujdurović, Edin Husić, Martin Milanič, Romeo Rizzi, Alexandru I. Tomescu, "Perfect phylogenies via branchings in acyclic digraphs and a generalization of Dilworth's theorem", arXiv:1701.05492 (2017): Section 1 (definitions of conflict, row split, MCRS and MDCRS), Section 2 (containment digraph, uncovered pairs, irreducible vertices, $B$-split, and the equivalence theorem). <https://doi.org/10.48550/arXiv.1701.05492> Published version: ACM Transactions on Algorithms 14 (2018) 1–26, <https://doi.org/10.1145/3182178>.
