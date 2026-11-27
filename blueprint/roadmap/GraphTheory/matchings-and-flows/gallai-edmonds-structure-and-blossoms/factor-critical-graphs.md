# Factor-critical graphs and near-perfect matchings

A finite simple graph $H$ with at least one vertex is *factor-critical* if for every vertex $v$ of $H$ the graph $H - v$ has a perfect matching. A *near-perfect matching* of a graph on $2k + 1$ vertices is a matching with $k$ edges, that is, a matching missing exactly one vertex. A factor-critical graph has an odd number of vertices, since $H - v$ has an even number of vertices, and it is connected: if it had two components $C_1 \ne C_2$, then choosing $v \in C_1$ would give every component other than $C_1$ a perfect matching and choosing $v \in C_2$ would give $C_1$ one, so every component would be even and $|V(H)|$ would be even. Every odd cycle and every complete graph on an odd number of vertices is factor-critical.

## Depends on

- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)

## Sources

- T. Gallai, "Neuer Beweis eines Tutte'schen Satzes", Magyar Tud. Akad. Mat. Kutato Int. Kozl. 8 (1963).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
