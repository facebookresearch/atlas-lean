# Connected components of a reciprocal best match graph

Let $(T,\sigma)$ be a rooted gene tree with leaf set $L$ and a surjective leaf colouring $\sigma : L \to S$ by species, $|S| \ge 2$ (every species of $S$ colours at least one leaf, as the source assumes throughout). A leaf $y$ is a *best match* of $x$ if $\operatorname{lca}(x,y) \preceq \operatorname{lca}(x,y')$ for every leaf $y'$ with $\sigma(y') = \sigma(y)$; $x$ and $y$ are *reciprocal best matches* if each is a best match of the other. The tree $(T,\sigma)$ *explains* the undirected coloured graph $(G,\sigma)$ on $L$ if $xy$ is an edge exactly when $\sigma(x) \ne \sigma(y)$ and $x, y$ are reciprocal best matches; $(G,\sigma)$ is a *reciprocal best match graph* (RBMG) if some leaf-coloured tree explains it.

**Theorem.** An undirected leaf-coloured graph $(G,\sigma)$ is an RBMG if and only if every connected component of $G$ is an RBMG and at least one connected component contains vertices of all colours of $S$.

Moreover, if $(G^*,\sigma^*)$ is a connected component with vertex set $L^*$ of an RBMG explained by $(T,\sigma)$, then $(G^*,\sigma^*)$ is itself an RBMG, explained by the restriction $T_{|L^*}$ of $T$ to $L^*$.

## Expansion

Restricting the tree to a component preserves all last-common-ancestor comparisons among its leaves, and no reciprocal best match crosses components, which gives the restriction statement. For the converse, the trees explaining the components are attached below a common root; the component containing all colours guarantees that every leaf keeps a best match of each colour inside its own component, so no spurious edge between components appears. The theorem reduces the characterization of RBMGs to connected ones, which the paper then treats colour class by colour class.

## Sources

- Manuela Geiß, Peter F. Stadler and Marc Hellmuth, *Reciprocal Best Match Graphs*, arXiv:1903.07920, Theorems 2 and 3 (Section "Connected Components"). <https://doi.org/10.48550/arXiv.1903.07920> Published version: Journal of Mathematical Biology 80 (2019) 865–953, <https://doi.org/10.1007/s00285-019-01444-2>.
