# Single-pass greedy maximal matching is a 1/2-approximate matching and 2-approximate vertex cover

On an insertion-only graph stream of an $n$-vertex graph $G$, consider the deterministic algorithm that maintains a set $M$, initially empty, and on arrival of $e_t = \{u, v\}$ adds $e_t$ to $M$ if and only if neither $u$ nor $v$ is an endpoint of an edge already in $M$. It stores at most $n/2$ edges, hence $O(n \log n)$ bits, and at the end of the stream:

1. $M$ is a maximal matching of $G$, so $|M| \ge \mu(G)/2$;
2. the set $V(M)$ of matched vertices is a vertex cover of $G$ with $|V(M)| = 2|M| \le 2\,\tau(G)$.

## Proof sketch

Matched vertices stay matched, so an edge rejected at its arrival has an endpoint matched at the end, which gives maximality and shows that $V(M)$ covers every edge. Every edge of a maximum matching $M^\star$ meets $V(M)$, and each edge of $M$ meets at most two edges of $M^\star$, so $\mu(G) = |M^\star| \le 2|M|$. Any vertex cover contains a distinct endpoint of each of the pairwise disjoint edges of $M$, so $\tau(G) \ge |M|$.

## Depends on

- [Approximate maximum matching and vertex cover in a graph stream](approximate-matching-in-graph-streams.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)

## Proof depends on

- [The greedy matching is maximal](../../../online-algorithms/online-bipartite-matching/greedy-all-maximal.md)
- [Greedy online matching is within a factor $2$ of the maximum](../../../online-algorithms/online-bipartite-matching/card-max-matching-le.md)
- [The edges APPROX-VERTEX-COVER takes form a maximal matching of the listed pairs](../../../approximation-algorithms/vertex-cover-2-approximation/approx-vertex-cover-matching.md)

## Sources

- Michael Kapralov, "Better bounds for matchings in the streaming model", SODA (2013), arXiv:1206.2269.
- Christian Konrad, Frédéric Magniez, Claire Mathieu, "Maximum Matching in Semi-Streaming with Few Passes", APPROX (2012), arXiv:1112.0184.
