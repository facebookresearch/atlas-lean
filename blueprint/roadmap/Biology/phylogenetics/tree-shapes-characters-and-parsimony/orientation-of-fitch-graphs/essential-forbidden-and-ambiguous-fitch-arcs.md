# Essential, forbidden and ambiguous separating edges and Fitch arcs

**Setting.** Let $T$ be a rooted gene tree with leaf set $L$ and $H \subseteq E(T)$ a set of horizontal-transfer edges. The connected components of $T - H$ induce a partition $\mathcal{P}(T,H)$ of $L$ into transfer-free classes. The (directed) *Fitch graph* $\mathbb{F}(T,H)$ on $L$ has an arc $(x,y)$ if and only if the path from $\mathrm{lca}_T(x,y)$ to $y$ contains an edge of $H$; its symmetrization is complete multipartite with parts $\mathcal{P}(T,H)$. A partition $\mathcal{P}$ of $L$ is *compatible* with $T$ if $\mathcal{P} = \mathcal{P}(T,H)$ for some *separating set* $H$.

For compatible $(T,\mathcal{P})$:

- an edge $h \in E(T)$ is *essential* if $h \in H$ for every separating set $H$, *forbidden* if $h \notin H$ for every separating set, and *ambiguous* otherwise;
- a pair $(A,B)$ of distinct classes is *essential*, *forbidden* or *ambiguous* according as $(A,B)$ is an arc of the quotient Fitch graph $\mathbb{F}(T,H)/\mathcal{P}$ for all, for no, or for some but not all separating sets $H$ (all arcs between $A$ and $B$ have the same status).
- the coloring $\varpi : V(T) \to \mathcal{P} \cup \{\emptyset\}$ sets $\varpi(v) = A$ if $v$ lies on the path between two leaves $x, y \in A$, and $\varpi(v) = \emptyset$ otherwise; $v$ is *colored* if $\varpi(v) \neq \emptyset$.

**Theorem.** Let $T$ and $\mathcal{P}$ be compatible.

1. (Tree edges.) An edge $vw \in E(T)$ is essential iff $\emptyset \neq \varpi(v) \neq \varpi(w) \neq \emptyset$, forbidden iff $\emptyset \neq \varpi(v) = \varpi(w)$, and ambiguous otherwise. There is a unique inclusion-maximal separating set $H^*$, and $vw \notin H^*$ iff $vw$ is forbidden.
2. (Fitch arcs.) For distinct $A, B \in \mathcal{P}$, writing $\preceq$ for the descendant order of $T$ and $V^0(T)$ for its inner vertices:
   - $(A,B)$ is essential iff some colored $v \in V^0(T)$ satisfies $\mathrm{lca}(B) \prec v \preceq \mathrm{lca}(A \cup B)$;
   - $(A,B)$ is forbidden iff $\mathrm{lca}(A) \prec \mathrm{lca}(B)$;
   - $(A,B)$ is ambiguous iff $\mathrm{lca}(A)$ and $\mathrm{lca}(B)$ are incomparable and no such colored inner vertex exists.
3. (Algorithm.) After $O(|L|)$ preprocessing, the status of any pair $(A,B)$ can be queried in constant time, so all pairs are classified in $O(|L| + |\mathcal{P}|^2)$ time.

## Expansion

A colored vertex lies on a path between two members of one class, so no transfer edge may sit on that path; between two vertices with different colors some transfer must separate the classes, and there is exactly one edge to put it on. Directing arcs reduces to asking whether a transfer must, may, or cannot occur on the path from $\mathrm{lca}(A \cup B)$ down to $\mathrm{lca}(B)$: if $\mathrm{lca}(A)$ lies below $\mathrm{lca}(B)$, the class $B$ spans the whole path and no transfer fits there; a colored vertex strictly inside the path forces one. The paper extends the classification to refinements of non-binary gene trees, giving an analogous constant-time query for r-essential, r-forbidden and r-ambiguous pairs.

## Sources

- David Schaller, Marc Hellmuth and Peter F. Stadler, "Orientation of Fitch Graphs and Reconciliation-Free Inference of Horizontal Gene Transfer in Gene Trees", SIAM Journal on Discrete Mathematics 37 (2023), 2172–2207, <https://doi.org/10.1137/22m150736x>; numbering as in arXiv:2112.00403: Definitions 2–5, Proposition 3, Theorems 1–3 and Corollaries 1, 5, 7.
