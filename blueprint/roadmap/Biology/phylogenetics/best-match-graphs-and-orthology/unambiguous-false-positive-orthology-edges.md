# Unambiguous false-positive orthology edges are exactly the hug-edges

Let $(\vec G, \sigma)$ be a best match graph with symmetric part $G$. For a tree $(T, \sigma)$ explaining it, an edge $xy$ of $G$ is **$(T, \sigma)$-false-positive** if $\mu(\mathrm{lca}_T(x, y))$ is a duplication for every reconciliation map $\mu$ of $(T, \sigma)$ to every species tree (Def. 10). It is **unambiguous false-positive (u-fp)** if it is $(T, \sigma)$-false-positive for every tree $(T, \sigma)$ explaining $(\vec G, \sigma)$ (Def. 11).

For distinct leaves $x, y$ let $v_x, v_y$ be the children of $\mathrm{lca}_T(x, y)$ with $x \preceq_T v_x$ and $y \preceq_T v_y$, and define the **color intersection**

$$S^{\cap}(x, y) = \sigma\big(L(T(v_x))\big) \cap \sigma\big(L(T(v_y))\big).$$

For an edge of a BMG it does not depend on the explaining tree (Lemma 11).

1. **Sufficient condition** (Prop. 1, Cor. 3). Every edge $xy$ of $(\vec G, \sigma)$ with $S^{\cap}(x, y) \neq \emptyset$ is u-fp.
2. **Binary case** (Thm. 4). If $(\vec G, \sigma)$ is explained by a binary tree $(T, \sigma)$, then for every edge $xy$ the statements "$xy$ is $(T, \sigma)$-false-positive", "$S^{\cap}(x, y) \neq \emptyset$" and "$xy$ is u-fp" are equivalent.
3. **Complete characterization** (Thm. 11). An edge $xy$ of a BMG is u-fp if and only if it is a **hug-edge** (Def. 16): the middle edge of a good quartet, the first edge of an ugly quartet, or an edge joining the ends or tails of an hourglass chain (Def. 14). Here quartets are the subgraphs of the BMG spanned by induced $P_4$s of $G$.
4. **No-hug graph** (Def. 17, Thm. 12). Deleting all hug-edges from $G$ yields the no-hug graph $\mathrm{NH}(\vec G, \sigma)$. It contains no u-fp edge, it contains $\Theta(T, t_\mu)$ for every explaining tree and every reconciliation map, and it can be computed in polynomial time.

## Depends on

- [Best match graph of a leaf-colored tree](best-match-graph.md)

## Expansion

If two children of a vertex $u$ share a color, every reconciliation maps $u$ to an edge of the species tree, i.e. to a duplication (Lemma 2), which gives item 1. Quartets are $P_4$s, which cannot occur in the cograph of true orthologs. Hourglasses capture false positives with empty color intersection, where a third subtree below $\mathrm{lca}_T(x, y)$ carries both colors and "bridges" the subtrees of $x$ and $y$. The polynomial algorithm avoids enumerating hourglass chains: it augments the unique least resolved tree of the BMG and reads off orthology from the extremal event labeling of the augmented tree (Thm. 10).

## Sources

- D. Schaller, M. Geiß, P. F. Stadler, et al., *Complete characterization of incorrect orthology assignments in best match graphs*, J. Math. Biol. (2021). <https://doi.org/10.1007/s00285-021-01564-8> (PMCID: PMC7894253)
