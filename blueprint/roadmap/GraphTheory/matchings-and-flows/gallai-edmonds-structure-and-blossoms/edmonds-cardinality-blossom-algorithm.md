# Correctness and running time of Edmonds' cardinality blossom algorithm

Edmonds' algorithm grows an $M$-alternating forest whose roots are all missed vertices, which start as outer, by scanning edges at outer (pseudo)vertices: an edge from an outer vertex to a vertex $y$ outside the forest (then $y$ is matched) adds $y$ as an inner vertex and its mate as an outer vertex; an edge between outer vertices of different trees yields an augmenting path; an edge between outer vertices of the same tree yields a blossom that is shrunk; and the search halts only when every edge at an outer vertex leads to an inner vertex, i.e. no edge joins an outer vertex to another outer vertex or to a vertex outside the forest. For every finite simple graph $G$ with $n$ vertices and $m$ edges:

1. the algorithm returns a maximum matching after at most $\lfloor n/2 \rfloor$ augmentations, and a direct implementation runs in $O(n^2 m)$ time;
2. when the final search halts, the set $X$ of inner vertices satisfies $|M| = \frac{1}{2}(n + |X| - o(G - X))$, so it certifies optimality through the Tutte-Berge formula;
3. at that moment $D(G)$ is the set of vertices that are outer or lie in a shrunken outer blossom, $A(G) = X$, and $C(G)$ is the set of vertices outside the forest.

This gives an explicit polynomial bound for the general matching decision problem being in P.

## Proof sketch

By the shrinking lemma, maximality is preserved under shrinking, and augmenting paths found in the shrunken graph lift to $G$, so each successful search increases $|M|$ by one and Berge's lemma certifies the final matching once a search fails. A failed search leaves no edge from an outer (pseudo)vertex to another outer (pseudo)vertex or to a vertex outside the forest; deleting the inner set $X$ leaves every outer pseudovertex as an odd, factor-critical component (a nested blossom) and the vertices outside the forest perfectly matched among themselves, so the number of missed vertices equals $o(G - X) - |X|$, i.e. equality in the odd-component bound; comparing with the Gallai-Edmonds theorem identifies $D, A, C$. Each search performs at most $n/2$ shrinkings and $O(m)$ scans per shrunken graph, giving $O(nm)$ per search and $O(n^2 m)$ overall.

## Depends on

- [Alternating forests, flowers and blossoms of a matching](alternating-forests-and-blossoms.md)
- [Augmenting path](../berge-s-lemma/is-augmenting-walk.md)
- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)
- [The Gallai-Edmonds partition D(G), A(G), C(G)](gallai-edmonds-partition.md)
- [General matching decision problem](../../../TheoryOfComputation/polynomial-time-problems/matching-in-general-graphs/matching-dec.md)

## Proof depends on

- [Edmonds' blossom shrinking lemma](edmonds-blossom-shrinking-lemma.md)
- [Every vertex set bounds the matching number through its odd components](odd-components-bound-matching-number.md)
- [Gallai-Edmonds structure theorem for maximum matchings](gallai-edmonds-structure-theorem.md)
- [Berge's lemma for matching subgraphs](../berge-s-lemma/berge-general.md)
- [Tutte-Berge min-max formula for the maximum matching size](tutte-berge-min-max-formula.md)

## Sources

- J. Edmonds, "Paths, trees, and flowers", Canadian Journal of Mathematics 17 (1965).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
