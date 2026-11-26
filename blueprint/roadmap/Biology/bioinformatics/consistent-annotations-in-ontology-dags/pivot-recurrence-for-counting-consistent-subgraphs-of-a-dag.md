# Pivot recurrence for counting consistent subgraphs of a DAG

**Setting.** An ontology is a finite directed acyclic graph $O = (V, E)$ with edges pointing from general to specific concepts (possibly several roots, possibly disconnected). A vertex set $S \subseteq V$ is **consistent** (satisfies the true-path rule) if $v \in S$ implies that every ancestor of $v$ is in $S$; the induced subgraph $O[S]$ is a consistent subgraph. Let $\mathrm{cdag}(O)$ be the number of consistent subgraphs (the empty one included), that is, the number of up-closed sets of the ancestor order. For $u \in V$ let $D^+(u)$ be $u$ with all its descendants, $A^+(u)$ be $u$ with all its ancestors, and $O[-S]$ the subgraph induced by $V \setminus S$.

**Bounds.** If $\ell$ is the number of leaves, $2^\ell \le \mathrm{cdag}(O) \le 2^{|V|}$; a chain on $|V|$ vertices has $|V| + 1$ consistent subgraphs.

**Trees.** For a rooted tree, the number $c(v)$ of consistent subtrees of the subtree at $v$ satisfies

$$c(v) = 1 + \prod_{w \text{ child of } v} c(w),$$

and a forest's count is the product over its trees, giving a linear-time algorithm.

**Pivot decomposition (Equation 1).** For any vertex $u$,

$$\mathrm{cdag}(O) = \mathrm{cdag}\big(O[-D^+(u)]\big) + \mathrm{cdag}\big(O[-A^+(u)]\big).$$

Recursing with multi-parent pivots until the graph is a forest yields an exact algorithm with running time $T(n) \le T(n-1) + T(n-3) + f(n)$; it is polynomial when the number of multi-parent vertices is $O(\log n)$.

**Reverse graph.** $\mathrm{cdag}(O) = \mathrm{cdag}(O^R)$, where $O^R$ reverses every edge.

## Expansion

Split consistent sets by whether they contain $u$. If $u \notin S$, consistency forbids every descendant of $u$, and $S$ is exactly a consistent set of $O[-D^+(u)]$. If $u \in S$, consistency forces all of $A^+(u)$ into $S$, and $S \setminus A^+(u)$ is an arbitrary consistent set of $O[-A^+(u)]$, since its vertices' remaining ancestors lie outside $A^+(u)$. In a tree the children's subtrees are independent, which gives the product, plus one for the empty set. For the reverse graph, $S \mapsto V \setminus S$ maps up-closed sets of $O$ bijectively to up-closed sets of $O^R$. In biomedical ontologies such as the Gene Ontology the count measures the size of the space of possible annotations, and is used to quantify the entropy of concept annotation spaces.

## Sources

- Y. Peng, Y. Jiang, P. Radivojac, "Enumerating consistent sub-graphs of directed acyclic graphs: an insight into biomedical ontologies", Bioinformatics 34(13) (2018) i313, Sections 3.3, 4.1-4.4 and 5.2, Algorithms 1-2, Equation (1), <https://doi.org/10.1093/bioinformatics/bty268>, PMCID PMC6022688.
