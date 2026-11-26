# A best match graph has a binary explanation iff it is hourglass-free

Let $(\vec G, \sigma)$ be a *properly* vertex-colored digraph: no arc joins two vertices of the same color (every best match graph is one). An **hourglass** in $(\vec G, \sigma)$ is the subgraph induced by four pairwise distinct vertices $x, x', y, y'$ such that (Def. 13)

1. $\sigma(x) = \sigma(x') \neq \sigma(y) = \sigma(y')$;
2. $xy$ and $x'y'$ are symmetric edges;
3. $(x, y')$ and $(y, x')$ are arcs;
4. $(y', x)$ and $(x', y)$ are not arcs.

Condition 1 and proper coloring rule out arcs between $x$ and $x'$ and between $y$ and $y'$, so the only arcs of an hourglass are those in conditions 2 and 3. A best match graph is **hourglass-free** if it contains no hourglass as an induced subgraph (Def. 20).

**Theorem** (Prop. 8, Cor. 6). A best match graph $(\vec G, \sigma)$ can be explained by a binary leaf-colored tree if and only if it is hourglass-free. In particular, it can be decided in polynomial time whether a BMG has a binary explanation.

Every hourglass-free BMG is also hexagon-free (Lemma 33). By the binary case of the u-fp characterization, the u-fp edges of an hourglass-free BMG are exactly its edges $xy$ with $S^{\cap}(x, y) \neq \emptyset$.

## Depends on

- [Best match graph of a leaf-colored tree](best-match-graph.md)
- [Unambiguous false-positive orthology edges are exactly the hug-edges](unambiguous-false-positive-orthology-edges.md)

## Expansion

An hourglass forces, in every explaining tree, a vertex $u$ with three distinct children such that the middle subtree carries both colors and separates the other two (Lemma 14); a binary vertex has only two children, which gives necessity. For sufficiency, assume an hourglass-free BMG has no binary explanation, so it is explained by a tree with a non-binary vertex $u$ that cannot be refined. Call an ordered set of $k \ge 2$ distinct children $v_1, \dots, v_k$ of $u$ with $k - 1$ distinct colors $c_1, \dots, c_{k-1}$ an *hf-pair* of order $k$ if $c_i$ occurs below $v_j$ exactly for $i \le j \le k - 1$ among the first $k - 1$ children and every $c_i$ occurs below $v_k$. Lemma 32 (non-refinability of $u$) gives an hf-pair of order $2$, and, using hourglass-freeness, extends any hf-pair of order $k$ to one of order $k + 1$ with a new child of $u$. Hence $u$ has arbitrarily many distinct children, contradicting the finiteness of the tree.

## Sources

- D. Schaller, M. Geiß, P. F. Stadler, et al., *Complete characterization of incorrect orthology assignments in best match graphs*, J. Math. Biol. (2021). <https://doi.org/10.1007/s00285-021-01564-8> (PMCID: PMC7894253)
