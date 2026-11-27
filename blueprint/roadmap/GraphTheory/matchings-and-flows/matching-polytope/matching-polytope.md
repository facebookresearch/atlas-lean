# Matching polytope

The matching polytope of a finite graph $G = (V, E)$ is

$$
P_{\mathrm{matching}}(G) = \operatorname{conv}\{\chi^M : M \text{ a matching in } G\} \subseteq \mathbb{R}^E .
$$

Matchings are subgraphs $M$ of $G$ in which every vertex of $M$ has exactly one neighbour in $M$, and $\chi^M$ is the [incidence vector](edge-incidence.md) of their edges; the empty matching gives the zero vector.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization* (CWI lecture notes), <https://homepages.cwi.nl/~lex/files/dict.pdf>, §5.4, eq. (29).
