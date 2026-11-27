# Isolating cut lemma with logarithmically many max-flow calls

Let $G = (V, E, w)$ be an undirected graph with $n$ vertices, $m$ edges and positive integer weights, and let $R \subseteq V$ with $|R| \ge 2$. There is a deterministic algorithm that computes, for every $v \in R$, the minimal minimum $v$-isolating cut $S_v^{*}$ using

1. $\lceil \log_2 |R| \rceil$ maximum-flow oracle calls on graphs with at most $n$ vertices and $m$ edges, and
2. one further oracle call on a graph $G_v$ for each $v \in R$, where $G_v$ is obtained from $G$ by contracting $V \setminus U_v$ into a single vertex $t_v$, and these graphs satisfy

$$
\sum_{v \in R} |V(G_v)| \le 2n, \qquad \sum_{v \in R} |E(G_v)| \le 2m,
$$

plus $O(m \log |R|)$ additional time. Under the superadditivity assumption on $\mathrm{MF}$, the total running time is $O(\log |R| \cdot \mathrm{MF}(n, m) + m \log |R|)$.

## Proof sketch

Compute the cuts $X_i$ of the bit-cut construction with one oracle call each and form the disjoint regions $U_v$. Because $S_v^{*} \subseteq U_v$, a minimum $v$-$t_v$ cut in $G_v$ that is inclusion-wise minimal on the side of $v$ is exactly $S_v^{*}$, and its value in $G_v$ equals its value in $G$ since contraction of $V \setminus U_v$ preserves every cut contained in $U_v$. Every edge of $G_v$ has an endpoint in $U_v$ and the regions are disjoint, so each edge of $G$ appears in at most two graphs $G_v$, which gives the size bounds; superadditivity then bounds the cost of the second batch by $\mathrm{MF}(2n, 2m)$.

## Depends on

- [Maximum-flow oracles and the max-flow call model for cut problems](max-flow-oracle-call-model.md)
- [Minimum isolating cuts of a terminal set](minimum-isolating-cuts.md)

## Proof depends on

- [Minimal minimum isolating cuts lie in disjoint bit-cut regions](bit-cut-region-containment.md)
- [Contraction preserves the minimum cut size](../../../../randomized-algorithms/karger-s-algorithm/is-min-cut-contract.md)
- [Max-flow min-cut theorem](../../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Chandra Chekuri, Kent Quanrud, "Isolating Cuts, (Bi-)Submodularity, and Faster Algorithms for Connectivity", ICALP (2021), arXiv:2103.12908.
