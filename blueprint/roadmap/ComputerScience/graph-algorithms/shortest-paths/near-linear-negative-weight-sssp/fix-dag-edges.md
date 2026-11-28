# FixDAGEdges: a linear-time price function for graphs whose negative edges join parts of an acyclic condensation

Let $G=(V,E,w)$ be a directed graph with integer weights and let $\mathcal{P}=\{V_1,V_2,\dots\}$ be a partition of $V$ such that (i) every induced subgraph $G[V_i]$ has no negative edge, and (ii) contracting each $V_i$ to a single node yields an acyclic graph. Then a price function $\phi:V\to\mathbb{Z}$ with $w_\phi(u,v)\ge 0$ for all $(u,v)\in E$, constant on each $V_i$, can be computed deterministically in $O(m+n)$ time.

## Proof sketch

Order the parts topologically in the contracted acyclic graph. Process them in this order and give all vertices of $V_i$ the common price $\phi(V_i)=\min\big(\{0\}\cup\{\phi(V_j)+w(u,v):(u,v)\in E,\ u\in V_j,\ v\in V_i,\ j\ne i\}\big)$, which makes every edge entering $V_i$ nonnegative. Edges inside $V_i$ keep their nonnegative weight because both endpoints get the same price, and edges leaving $V_i$ are handled when their head part is processed. Each edge is inspected once.

## Depends on

- [Price functions, reduced edge weights, and valid reweightings of a directed graph](price-functions-and-reduced-weights.md)
- [SCC partition](../../traversal-and-connectivity/strongly-connected-components/is-sccpartition.md)
- [Acyclic condensation](../../traversal-and-connectivity/strongly-connected-components/condensation-acyclic.md)

## Proof depends on

- [Shortest paths in a DAG with a topology check](../shortest-paths-in-directed-acyclic-graphs/dag-shortest-paths.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
