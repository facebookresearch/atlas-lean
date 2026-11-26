# Markov graph of irreversible event accumulation on a tree is a line graph

**Event-accumulation model.** Let $T = (V, A)$ be a finite rooted tree with arcs directed away from the root and $p = |A| \ge 2$ arcs. Each arc $a_i = (u_i, v_i)$ carries one event type $E_i$ (for example a somatic mutation, under the infinite-sites/perfect-phylogeny assumption), and $i \mapsto a_i$ is a bijection. A unit's history (lineage) is a directed path from the root, identified with the node $Z \in V$ it has reached. Events are irreversible and inherited, so the observed binary vector is

$$Y_i = \mathbf 1[Z \in S(v_i)], \qquad i = 1,\dots,p,$$

where $S(v)$ is the subtree rooted at $v$. Assume **positivity over nodes**: $\rho(z) = \mathbb P(Z = z) > 0$ for every $z \in V$, so lineages can be observed at any stage, including internal nodes and the root. The **Markov graph** $\mathcal G(T)$ on $\{1,\dots,p\}$ has an edge $\{i,j\}$ unless $Y_i \perp\!\!\!\perp Y_j \mid Y_{\{1,\dots,p\}\setminus\{i,j\}}$.

**Theorem.**

1. $\mathcal G(T)$ is chordal (decomposable).
2. Any two distinct maximal cliques of $\mathcal G(T)$ share at most one vertex.
3. Every vertex lies in at most two maximal cliques.
4. $\mathcal G(T)$ has a junction tree all of whose separators are singletons.

Equivalently, $\mathcal G(T) = L(T_u)$ is the **line graph** of the underlying undirected tree $T_u$: events $i$ and $j$ are conditionally dependent exactly when their arcs share a node. The maximal cliques are the blocks of arcs at each non-leaf node (the arc entering it together with the arcs leaving it). The arc entering a node that is neither the root nor a leaf is the singleton separator between the block of that node and the block of its parent.

**Leaf-only sampling collapses the structure.** If instead $Z$ is supported only on the leaves (every root-to-leaf path having positive probability), then $i$ and $j$ are adjacent if and only if $a_i, a_j$ are sibling arcs whose heads are both leaves. The Markov graph is then a disjoint union of cliques, one per node with at least two leaf children, and most of the tree structure becomes invisible.

So decomposable graphical models with singleton separators are not just a computational convenience: they are forced by irreversible accumulation along a branching history, observed at random stages.

## Expansion

The key is a hinge-screening identity. For a non-root node $v$, the indicator of the arc entering $v$ separates the events strictly below $v$ from all other events. Given that $v$ was not reached, every event below $v$ is $0$. Given that it was reached, all events on the path to $v$ are $1$, and the remaining events below and outside $S(v)$ depend on $Z$ only through which side it fell on. This screening yields pairwise conditional independence for non-adjacent arcs. Positivity ensures that arcs sharing a node are genuinely dependent, because a lineage can stop at the shared node. The singleton separations then give a decomposable factorization with the stated clique structure, which is exactly that of a line graph of a tree.

## Sources

- Rodrigo Labouriau, "Graphical Models Induced by Irreversible Event Accumulation on Trees", arXiv (2026). Section 2 (event tree, lineage, positivity assumption, Proposition 2.5 on leaf-only sampling, Definition 2.7), Section 3 (Theorem 3.1 and the line-graph remark), Section 4 (hinge-screening lemma), Section 6 (Propositions 6.1 and 6.3). <https://doi.org/10.48550/arXiv.2610.40127>
