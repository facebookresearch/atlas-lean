# Approximability of minimum conflict-free row split

**Setting.** Use the minimum conflict-free row split problems MCRS (minimize the number of rows, $\gamma(M)$) and MDCRS (minimize the number of distinct rows, $\eta(M)$), and the containment digraph $D_M$ of column supports, from [Conflict-free row splits are minimum uncovering branchings](conflict-free-row-splits-are-minimum-uncovering-branchings.md). Let $h(M)$ be the height of $D_M$ (the largest number of vertices on a directed path) and $\mathrm{wdt}(M)$ its width (the largest antichain); let $k$ be the number of distinct columns.

**Theorem.**

1. MCRS and MDCRS (equivalently minimum uncovering branching and minimum irreducible branching) are APX-hard, even on instances of height $2$.
2. A binary matrix is conflict-free if and only if its column supports form a laminar family, and every laminar family on $m$ points has at most $2m$ members; so a conflict-free matrix with $m$ rows has $k\le 2m$ distinct columns. This yields a $2$-approximation for MDCRS in time $O(mnk)$; hence MDCRS is APX-complete.
3. For every branching $B$ of $D_M$, the $B$-split of $M$ has at most $h(M)\,\gamma(M)$ rows; in particular the empty branching gives an $h(M)$-approximation for MCRS.
4. Any algorithm that returns the split of a linear branching consisting of $\mathrm{wdt}(M)$ paths is a $\mathrm{wdt}(M)$-approximation for MCRS.
5. The optimal linear-branching heuristic is not an $(h-\epsilon)$-approximation on instances of height $h$: for complete $d$-ary laminar instances the ratio is $h-(h-1)/d$.

## Depends on

- [Conflict-free row splits are minimum uncovering branchings](conflict-free-row-splits-are-minimum-uncovering-branchings.md)

## Proof depends on

- [Minimum price chain partitions and towers of antichains](minimum-price-chain-partitions-and-towers-of-antichains.md)

## Expansion

APX-hardness comes from $L$-reductions from vertex cover in cubic graphs: rows are the edges of the graph plus two extra elements, and the column supports encode vertices, so that the containment digraph has height $2$ and optimal branchings correspond to minimum vertex covers. For the $2$-approximation, the number of distinct rows of any conflict-free split is at least half the number of distinct columns, since the split's columns are laminar; splitting each row of the distinct-column reduction of $M$ into unit rows (one per $1$-entry) and duplicating columns back gives a conflict-free split with at most $k$ distinct rows, hence at most $2\eta(M)$. The height bound holds because each row $r$ lies in at most $h(M)$ supports along any chain, so the uncovered pairs of $r$ can be charged to the rows of an optimal split. The width bound uses the min-max theorem for chain partitions: a linear branching with $\mathrm{wdt}(M)$ paths leaves each row uncovered at most once per path.

## Sources

- Ademir Hujdurović, Edin Husić, Martin Milanič, Romeo Rizzi, Alexandru I. Tomescu, "Perfect phylogenies via branchings in acyclic digraphs and a generalization of Dilworth's theorem", arXiv:1701.05492 (2017): Section 4.1 (APX-hardness theorem and propositions, $L$-reductions), Section 4.2 (laminar characterization, laminar size bound, corollary $k\le 2m$, $2$-approximation theorem), Section 4.3 (height and width approximation theorems and the $d$-ary tightness example). <https://doi.org/10.48550/arXiv.1701.05492> Published version: ACM Transactions on Algorithms 14 (2018) 1–26, <https://doi.org/10.1145/3182178>.
