# A best match graph has a binary explanation iff it is hourglass-free

An **hourglass** in a vertex-colored digraph $(\vec G, \sigma)$ is the subgraph induced by four distinct vertices $x, x', y, y'$ such that (Def. 13)

1. $\sigma(x) = \sigma(x') \neq \sigma(y) = \sigma(y')$;
2. $xy$ and $x'y'$ are symmetric edges;
3. $(x, y')$ and $(y, x')$ are arcs;
4. $(y', x)$ and $(x', y)$ are not arcs.

A best match graph is **hourglass-free** if it contains no hourglass as an induced subgraph (Def. 20).

**Theorem** (Prop. 8, Cor. 6). A best match graph $(\vec G, \sigma)$ can be explained by a binary leaf-colored tree if and only if it is hourglass-free. In particular, it can be decided in polynomial time whether a BMG has a binary explanation.

Every hourglass-free BMG is also hexagon-free (Lemma 33). By the binary case of the u-fp characterization, the u-fp edges of an hourglass-free BMG are exactly its edges $xy$ with $S^{\cap}(x, y) \neq \emptyset$.

## Depends on

- [Best match graph of a leaf-colored tree](best-match-graph.md)
- [Unambiguous false-positive orthology edges are exactly the hug-edges](unambiguous-false-positive-orthology-edges.md)

## Expansion

An hourglass forces, in every explaining tree, a vertex $u$ with three distinct children such that the middle subtree carries both colors and separates the other two (Lemma 14); a binary vertex has only two children, which gives necessity. For sufficiency, assume the BMG is explained only by trees with a non-refinable non-binary vertex; Lemma 32 then produces an ordered sequence of children and connecting colors that can be extended until it closes into an induced hourglass, a contradiction.

## Sources

- D. Schaller, M. Geiß, P. F. Stadler, et al., *Complete characterization of incorrect orthology assignments in best match graphs*, J. Math. Biol. (2021). <https://doi.org/10.1007/s00285-021-01564-8> (PMCID: PMC7894253)
