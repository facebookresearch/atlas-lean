# Odd components and the Tutte deficiency of a vertex set

Let $G = (V, E)$ be a finite simple graph and let $\nu(G)$ denote the largest number of edges of a matching of $G$. A matching $M$ *misses* a vertex $v$ if no edge of $M$ contains $v$. For $X \subseteq V$ let $o(G - X)$ be the number of connected components of $G - X$ that have an odd number of vertices, and define the *deficiency* of $X$ as

$$
\operatorname{def}_G(X) = o(G - X) - |X| .
$$

The *deficiency* of $G$ is $\operatorname{def}(G) = \max_{X \subseteq V} \operatorname{def}_G(X)$. Taking $X = \emptyset$ shows $\operatorname{def}(G) \ge o(G) \ge 0$, and $\operatorname{def}_G(X) \equiv |V| \pmod 2$ for every $X$.

## Sources

- W. T. Tutte, "The factorization of linear graphs", Journal of the London Mathematical Society 22 (1947).
- C. Berge, "Sur le couplage maximum d'un graphe", Comptes Rendus de l'Academie des Sciences Paris 247 (1958).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
