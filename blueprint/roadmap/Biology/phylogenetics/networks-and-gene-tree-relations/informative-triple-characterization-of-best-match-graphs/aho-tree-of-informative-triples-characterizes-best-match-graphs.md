# The Aho tree of informative triples characterizes best match graphs

**Setting.** Let $(T, \sigma)$ be a rooted phylogenetic tree with leaf set $L$ and a leaf colouring $\sigma : L \to S$ (genes coloured by species). For $x, y \in L$ with $\sigma(x) \ne \sigma(y)$, $y$ is a best match of $x$ if $\mathrm{lca}_T(x, y) \preceq_T \mathrm{lca}_T(x, y')$ for every $y'$ with $\sigma(y') = \sigma(y)$. The colored best match graph $G(T, \sigma)$ has vertex set $L$ and an arc $xy$ for every best match. A vertex-coloured digraph $(G, \sigma)$ with $n$ colours is an $n$-cBMG if $(G, \sigma) = G(T, \sigma)$ for some tree, which is then said to *explain* it. An inner edge $e$ of an explaining tree is *redundant* if contracting it gives a tree that still explains $(G, \sigma)$; a tree without redundant edges is *least resolved*.

**Informative triples.** A rooted triple $ab \mid b'$ on pairwise distinct vertices is *informative* for $(G, \sigma)$ if $\sigma(a) \ne \sigma(b) = \sigma(b')$, $ab \in E(G)$ and $ab' \notin E(G)$. Write $R(G, \sigma)$ for the set of informative triples, and $\mathrm{Aho}(R)$ for the tree on $L$ returned by the BUILD (Aho) algorithm when the triple set $R$ is consistent.

**Theorem.** A vertex-coloured digraph $(G, \sigma)$ is an $n$-cBMG if and only if

$$G\bigl(\mathrm{Aho}(R(G, \sigma)), \sigma\bigr) = (G, \sigma).$$

Moreover, for an $n$-cBMG, $(\mathrm{Aho}(R(G, \sigma)), \sigma)$ is the unique least resolved tree that explains it. No connectedness assumption is needed.

**Supporting facts.**

- *Triples are forced.* If $(G, \sigma)$ is an $n$-cBMG and $ab \mid b'$ is informative, then every explaining tree displays $ab \mid b'$, i.e. $\mathrm{lca}_T(a, b) \prec_T \mathrm{lca}_T(a, b') = \mathrm{lca}_T(b, b')$.
- *Redundant edges.* For an $n$-cBMG explained by $(T, \sigma)$, an edge $uv$ with $v \prec_T u$ is redundant iff it is an inner edge and no arc $ab \in E(G)$ has $\mathrm{lca}_T(a, b) = v$ and $\sigma(b) \in \sigma(L(T(u)) \setminus L(T(v)))$. Equivalently, an inner edge is non-redundant iff some informative triple distinguishes it, so every inner edge of a least resolved tree is distinguished by an informative triple.
- *Heredity.* If $(T, \sigma)$ explains (is least resolved for) an $n$-cBMG, then each subtree $T(u)$ explains (is least resolved for) the subgraph of $G$ induced by $L(T(u))$.

**Recognition.** To decide whether $(G, \sigma)$ is an $n$-cBMG it suffices to build $T = \mathrm{Aho}(R(G, \sigma))$, construct $G(T, \sigma)$ and compare it with $(G, \sigma)$. Building the Aho tree takes $O(|E|\,|L| \log^2 |L|)$ time with a fast compatibility algorithm; constructing $G(T, \sigma)$ and checking equality take $O(|L|^2)$, so the construction of $T$ dominates.

## Expansion

The key step is that, for a least resolved tree $T$ of an $n$-cBMG and any inner vertex $u$ with child $v$, the leaf set $L(T(v))$ is exactly one connected component of the Aho graph $[R|_{L(T(u))}, L(T(u))]$ built from the informative triples restricted to $L(T(u))$. Connectivity inside $L(T(v))$ follows by induction on $|L|$, using the informative triple that distinguishes the edge $uv$ to join the components of the children of $v$. No Aho-graph edge can leave $L(T(v))$, since such an edge would come from an informative triple whose two closer leaves have last common ancestor $u$, which the tree cannot display. BUILD therefore splits the leaves exactly as $T$ does at every vertex, so any least resolved tree equals $\mathrm{Aho}(R(G, \sigma))$. One exists because contracting redundant edges one at a time terminates, which gives uniqueness and the forward direction. The converse holds because $G(\mathrm{Aho}(\cdot), \sigma)$ is by definition a best match graph. The theorem also implies the 2-colour triple characterization and the existence of unique least resolved trees in the original best match graph paper, and it avoids building least resolved trees for every 2-coloured induced subgraph.

## Sources

- D. Schaller, M. Geiß, E. Chávez, M. González Laffitte, A. López Sánchez, B. M. R. Stadler, D. I. Valdivia, M. Hellmuth, M. Hernández Rosales, P. F. Stadler, "Corrigendum to 'Best match graphs'", Journal of Mathematical Biology 82 (2021) 47, Definition 1, Lemmas 1–5, Corollary 1, Proposition 1, Theorem 1 and the corrected Algorithm 1, <https://doi.org/10.1007/s00285-021-01601-6> (PMC8021527).
- M. Geiß et al., "Best match graphs", Journal of Mathematical Biology 78 (2019) 2015–2057, <https://doi.org/10.1007/s00285-019-01332-9>.
