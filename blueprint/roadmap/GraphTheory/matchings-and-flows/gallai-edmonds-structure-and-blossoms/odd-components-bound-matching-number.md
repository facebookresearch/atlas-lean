# Every vertex set bounds the matching number through its odd components

Let $G = (V, E)$ be a finite simple graph. For every $X \subseteq V$, every matching of $G$ misses at least $\operatorname{def}_G(X)$ vertices. Equivalently,

$$
\nu(G) \le \frac{|V| + |X| - o(G - X)}{2} \qquad \text{for every } X \subseteq V .
$$

## Proof sketch

Let $M$ be a matching and $K$ an odd component of $G - X$. Since $|K|$ is odd, $M$ cannot match all vertices of $K$ inside $K$, so some vertex of $K$ is either missed by $M$ or matched by an edge to $X$. Each vertex of $X$ is matched to at most one vertex, so at most $|X|$ odd components are served by edges to $X$, and the remaining at least $o(G-X) - |X|$ odd components each contain a missed vertex. Hence $|V| - 2|M| \ge \operatorname{def}_G(X)$.

## Depends on

- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)

## Sources

- C. Berge, "Sur le couplage maximum d'un graphe", Comptes Rendus de l'Academie des Sciences Paris 247 (1958).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
