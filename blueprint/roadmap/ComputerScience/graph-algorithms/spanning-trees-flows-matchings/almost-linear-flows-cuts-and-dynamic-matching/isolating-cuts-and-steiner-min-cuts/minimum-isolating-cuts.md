# Minimum isolating cuts of a terminal set

Let $G = (V, E, w)$ be a connected undirected graph with positive edge weights, $R \subseteq V$ with $|R| \ge 2$, and $v \in R$. A set $S \subseteq V$ is a *$v$-isolating cut* (with respect to $R$) if $S \cap R = \{v\}$. A *minimum $v$-isolating cut* minimizes $w(\partial S)$ among all $v$-isolating cuts; its value is the minimum $(v, R \setminus \{v\})$-cut value. The *minimum isolating cuts problem* asks, for every $v \in R$ simultaneously, for a minimum $v$-isolating cut $S_v$. Every $v$-isolating cut is an $R$-Steiner cut, hence

$$
\lambda_R(G) \le \min_{v \in R} w(\partial S_v).
$$

## Depends on

- [Steiner minimum cuts of a terminal set](steiner-minimum-cut.md)
- [Edge cuts separating two vertices](../../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stedge-cut.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Chandra Chekuri, Kent Quanrud, "Isolating Cuts, (Bi-)Submodularity, and Faster Algorithms for Global Connectivity Problems", ICALP (2021), arXiv:2103.12908.
