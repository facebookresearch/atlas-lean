# Deterministic almost-linear minimum cut in weighted graphs (Li)

There is a deterministic algorithm that computes a global minimum cut of a connected undirected graph with $n$ vertices, $m$ edges and polynomially bounded positive weights (all in $[n^{-O(1)}, n^{O(1)}]$) in $m^{1+o(1)}$ time. Along the way it deterministically constructs a family of $n^{o(1)}$ trees on the vertex set $V$, not necessarily subgraphs of $G$, one of which $2$-respects a global minimum cut. Here, following Li (Definition 1.2), a cut $\emptyset \ne S \subsetneq V$ of $G$ *$2$-respects* a tree $T$ on $V$ if $|\partial_T S| \le 2$, that is, at most two edges of $T$ have exactly one endpoint in $S$; this counts the crossing edges of $T$ itself, whether or not they are edges of $G$, and for a spanning tree $T$ of $G$ it is the notion $|\partial S \cap E(T)| \le 2$ of the linked page on respecting cuts.

## Proof sketch

The only randomized step of Karger's algorithm is the sampled skeleton. Li derandomizes the Benczur-Karger style sampling by the method of pessimistic estimators: an expander decomposition hierarchy supplies a small family of potential functions that dominate the failure probability of all cuts simultaneously, so that the sample can be fixed edge by edge while keeping every approximately minimum cut well approximated. The result is an unweighted skeleton $H$ on $V$ and a scale $W$ with $W\,|\partial_H S| \ge (1 - \epsilon)\lambda$ for every cut $\emptyset \ne S \subsetneq V$, where $\lambda$ is the minimum cut value of $G$, and with the upper bound $W\,|\partial_H S^*| \le (1 + \epsilon)\lambda$ guaranteed only for the minimum cuts $S^*$ of $G$. With $\epsilon = 0.01$ every minimum cut of $G$ is a $7/6$-approximate minimum cut of $H$, and $H$ has minimum cut $n^{o(1)}$, so Karger's deterministic tree packing on $H$ gives $n^{o(1)}$ trees on $V$ one of which $2$-respects a minimum cut of $G$. These trees are spanning trees of $H$ and need not be subgraphs of $G$, so the subgraph-based respecting-cut results do not apply to them directly; instead Karger's dynamic program (Li, Theorem 1.4), which, given $G$ and any tree $T$ on $V$, deterministically finds in $O(m\log^2 n)$ time the minimum-weight cut of $G$ that $2$-respects $T$ in the sense $|\partial_T S| \le 2$, is applied to each tree (Li, Theorem 1.3 for the tree family, Claim 1.6 for the skeleton conditions).

## Depends on

- [Cuts that k-respect a spanning tree](cuts-k-respecting-a-spanning-tree.md)
- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Proof depends on

- [Karger's skeleton: logarithmically many trees one of which 2-respects the minimum cut](karger-skeleton-tree-family.md)
- [A near-maximum tree packing has many trees that 2-respect a minimum cut](tree-packing-two-respects-minimum-cut.md)
- [Weighted expander decompositions with volumes measured in the host graph](expander-decomposition.md)

## Sources

- Jason Li, "Deterministic Mincut in Almost-Linear Time", STOC (2021), arXiv:2106.05513, Theorem 1.1, Definition 1.2, Theorems 1.3–1.5 and Claim 1.6.
- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
