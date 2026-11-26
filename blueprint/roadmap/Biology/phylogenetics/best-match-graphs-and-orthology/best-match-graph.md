# Best match graph of a leaf-colored tree

Let $T$ be a planted phylogenetic (gene) tree with leaf set $L(T)$ and let $\sigma : L(T) \to S$ be a surjective coloring that assigns each gene the species in which it resides; $(T, \sigma)$ is a *leaf-colored tree*. Write $u \preceq_T v$ if $v$ lies on the path from the root to $u$, and $\mathrm{lca}_T$ for the last common ancestor.

A leaf $y$ is a **best match** of the leaf $x$ (Def. 1) if $\sigma(x) \neq \sigma(y)$ and

$$\mathrm{lca}_T(x, y) \preceq_T \mathrm{lca}_T(x, y') \quad \text{for every leaf } y' \text{ with } \sigma(y') = \sigma(y).$$

The leaves $x$ and $y$ are **reciprocal best matches** if each is a best match of the other.

The **best match graph** (BMG) $\vec G(T, \sigma)$ is the vertex-colored digraph on $L(T)$ with an arc $(x, y)$ exactly when $y$ is a best match of $x$. Its symmetric part $G(T, \sigma)$, which keeps $xy$ iff both $(x, y)$ and $(y, x)$ are arcs, is the **reciprocal best match graph** (RBMG). A vertex-colored digraph $(\vec G, \sigma)$ is a BMG if $(\vec G, \sigma) = \vec G(T, \sigma)$ for some leaf-colored tree, which is then said to *explain* it (Def. 2).

A reconciliation map $\mu$ of $(T, \sigma)$ into a species tree labels each inner vertex of $T$ as a speciation ($\bullet$) or a duplication ($\square$), giving an event labeling $t_\mu$. The **orthology graph** $\Theta(T, t_\mu)$ joins $x$ and $y$ iff $t_\mu(\mathrm{lca}_T(x, y)) = \bullet$ (Def. 6). Then (Thm. 2)

$$\Theta(T, t_\mu) \subseteq G(T, \sigma) \subseteq \vec G(T, \sigma),$$

so a BMG never misses an orthologous pair: every error of BMG-based orthology inference is a false positive. Orthology graphs are exactly the cographs (Thm. 1), so every induced path $P_4$ of an RBMG contains a false-positive edge.

## Expansion

If $x$ and $y$ are orthologs, their last common ancestor is a speciation. A gene $y'$ of species $\sigma(y)$ closer to $x$ would sit in the subtree of $x$, and the two subtrees below the speciation would then share the color $\sigma(y)$, which forces a duplication. Hence $y$ is a best match of $x$ and vice versa. Best matches are neither unique nor transitive, in contrast to the clusters-of-orthologous-groups picture.

## Sources

- D. Schaller, M. Geiß, P. F. Stadler, et al., *Complete characterization of incorrect orthology assignments in best match graphs*, J. Math. Biol. (2021). <https://doi.org/10.1007/s00285-021-01564-8> (PMCID: PMC7894253)
