# Minimum 2-respecting cut of a spanning tree in O(m log n) deterministic time

Given a connected undirected graph $G = (V, E, w)$ with $n$ vertices, $m$ edges and positive weights, and a spanning tree $T$ of $G$, a minimum $2$-respecting cut of $T$ (with its value) can be computed deterministically in $O(m \log n)$ time on the word RAM (Gawrychowski-Mozes-Weimann). Karger's original dynamic program achieves $O(m \log^2 n)$ time, and the approach of Mukhopadhyay-Nanongkai evaluates only $\tilde O(n)$ candidate pairs of tree edges.

## Proof sketch

Root $T$ and let $T_v$ be the vertex set of the subtree below $v$ and $C(v) = w(\partial T_v)$. For incomparable $u, v$ the cut $T_u \cup T_v$ has weight $C(u) + C(v) - 2w(T_u, T_v)$, and for $v$ below $u$ the cut $T_u \setminus T_v$ has weight $C(u) + C(v) - 2w(T_v, V \setminus T_u)$; all these quantities are sums over edges classified by lowest common ancestors of their endpoints. A heavy-path decomposition reduces the search to $O(\log n)$ path-to-path problems, each of which is solved by a monotonicity (Monge-like) argument with a data structure supporting path additions and minimum queries in logarithmic time.

## Depends on

- [Cuts that k-respect a spanning tree](cuts-k-respecting-a-spanning-tree.md)
- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Lowest common ancestors via range minimum queries](../../../../data-structures/range-query-structures/advanced-data-structures/lowest-common-ancestors-via-range-minimum.md)

## Sources

- Pawel Gawrychowski, Shay Mozes, Oren Weimann, "Minimum Cut in O(m log^2 n) Time", ICALP (2020), arXiv:1911.01145.
- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
- Sagnik Mukhopadhyay, Danupon Nanongkai, "Weighted Min-Cut: Sequential, Cut-Query and Streaming Algorithms", STOC (2020), arXiv:1911.01651.
