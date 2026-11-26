# Horizontal and ranked SPR treespaces

**Ranked trees.** A ranked tree on leaves $\{l_1, \dots, l_n\}$ is a rooted binary phylogenetic tree whose $n - 1$ internal nodes carry distinct ranks $1, \dots, n-1$ increasing towards the root (the root has rank $n - 1$). It can be written as the list $[C_1, \dots, C_{n-1}]$ of the clusters induced by the nodes of rank $1, \dots, n-1$. Edges are written $(u^+, u^-)$ for parent $u^+$ and child $u^-$.

**Moves.** A **horizontal SPR (HSPR) move** prunes the subtree below a non-root edge, removes the node $i$ (of rank $i$) at its top, and reattaches the subtree at a new node of the same rank $i$ on another edge spanning that rank. Formally (Theorem 2), $T'$ with

$$E(T') = E(T) \setminus \{(i^+, i), (i, i^-), (j^+, j^-)\} \cup \{(i^+, i^-), (j^+, i), (i, j^-)\}$$

is an HSPR neighbour of $T$ iff $(i^+, i), (i, i^-), (j^+, j^-) \in E(T)$ and $j^- \prec i \prec j^+$. A **rank move** swaps the ranks of two nodes with consecutive ranks that are not joined by an edge. The graph **HSPR** joins trees differing by one HSPR move; **RSPR** joins trees differing by one HSPR move or one rank move. Their path metrics are $d_{\mathrm{HSPR}}$ and $d_{\mathrm{RSPR}}$.

**Results.**

- (Theorem 4, Corollary 1) HSPR and RSPR are connected, so $d_{\mathrm{HSPR}}$ and $d_{\mathrm{RSPR}}$ are metrics; already HSPR moves alone connect any two trees.
- (Theorem 5) A tree $T$ with $k$ pairs of consecutive ranks admitting a rank move has exactly $(n-1)(n-2)$ HSPR neighbours and $(n-1)(n-2) + k$ RSPR neighbours.
- (Theorem 6) There are trees $T, R$ with $d_{\mathrm{HSPR}}(T, R) \ge \lceil n/2 \rceil$.
- (Theorem 1, background) For unranked rooted trees, deciding $d_{\mathrm{SPR}}(T, R) \le k$ is NP-complete.

## Expansion

An HSPR move keeps every node at its rank, so it changes only the cluster at rank $i$ and those above it that contained or now contain the moved subtree (Theorem 3 lists the exact update). Connectivity follows from a bottom-up construction: for $k = 1, \dots, n-2$, at most two HSPR moves at rank $k$ make the cluster at rank $k$ agree with the target while leaving lower ranks untouched. For the neighbour count, at each rank $i$ there are two subtrees that can be pruned and, after pruning, $n - 2$ edges spanning rank $i$ other than the one removed; summing over ranks gives $(n-1)(n-2)$, independent of tree shape, while rank moves add one neighbour per admissible rank swap. These spaces model the treespace explored by Bayesian time-tree samplers, where SPR-like proposals must respect node heights.

## Sources

- L. Collienne, C. Whidden, A. Gavryushkin, "Ranked subtree prune and regraft", Bulletin of Mathematical Biology 86 (2024) 24, Section 2 and Theorems 1–6, Corollary 1, <https://doi.org/10.1007/s11538-023-01244-2> (PMC10830682).
