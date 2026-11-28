# Steiner minimum cuts of a terminal set

Let $G = (V, E, w)$ be a connected undirected graph with positive edge weights and let $R \subseteq V$ be a set of terminals with $|R| \ge 2$. A set $S \subseteq V$ is an *$R$-Steiner cut* if $S \cap R \ne \emptyset$ and $R \not\subseteq S$, that is, the edges $\partial S$ separate at least one pair of terminals. The *Steiner minimum cut value* is

$$
\lambda_R(G) = \min \{\, w(\partial S) : S \subseteq V,\ \emptyset \ne S \cap R \ne R \,\}.
$$

For $R = \{s, t\}$ this is the minimum $s$-$t$ cut value $\lambda_G(s,t)$, and for $R = V$ it is the global edge connectivity $\lambda(G)$, the weight of a global minimum cut. A global minimum cut $S$ is *trivial* if $|S| = 1$ or $|V \setminus S| = 1$.

## Depends on

- [Minimum cut size](../../../../randomized-algorithms/karger-s-algorithm/is-min-cut.md)
- [Edge cuts separating two vertices](../../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stedge-cut.md)
- [Cut capacity](../../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/cut-capacity.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Matthew Ding, Jason Li, "Deterministic Minimum Steiner Cut in Maximum Flow Time", ESA (2024), LIPIcs, doi:10.4230/LIPIcs.ESA.2024.46, arXiv:2312.16415.
