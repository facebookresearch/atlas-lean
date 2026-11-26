# Unsatisfiable relations of a root partition and consistent top-down BMG editing

**Setting.** Let $(\vec G=(V,E),\sigma)$ be a properly vertex-colored digraph (genes colored by species). For a leaf-colored tree $T$ on $V$ let $\vec G(T,\sigma)$ be its best match graph (BMG): $(x,y)$ is an arc iff $\sigma(x)\ne\sigma(y)$ and $y$ is a closest relative of $x$ among genes of color $\sigma(y)$. *BMG editing* asks for a minimum set of arc insertions and deletions turning $(\vec G,\sigma)$ into a BMG (an NP-hard problem). For a partition $\mathscr{V}=\{V_1,\dots,V_k\}$ of $V$, $k\ge2$, let $\mathscr{T}(\mathscr{V})$ be the trees whose root's children have leaf sets exactly $V_1,\dots,V_k$. The **unsatisfiable relations** $U(\vec G,\mathscr{V})$ are the ordered pairs $(x,y)$ that must be edited for every $T\in\mathscr{T}(\mathscr{V})$ (arcs absent from every $\vec G(T,\sigma)$, or non-arcs present in every one), and $c(\vec G,\mathscr{V})=|U(\vec G,\mathscr{V})|$ is the **UR-cost** of the partition.

**Theorem.**

*(1)* *(Explicit form.)* $U(\vec G,\mathscr{V})$ is the disjoint union of

$$\begin{aligned}U_1&=\{(x,y)\in E:\ x\in V_i,\ y\notin V_i,\ \sigma(y)\in\sigma(V_i)\},\\ U_2&=\{(x,y)\notin E:\ x\in V_i,\ y\notin V_i,\ \sigma(y)\notin\sigma(V_i)\},\\ U_3&=\{(x,y)\notin E:\ x\ne y\in V_i,\ V_i[\sigma(y)]=\{y\}\},\end{aligned}$$

so it can be computed in $O(|V|^2)$ time without enumerating trees.

*(2)* *(Edits forced by every tree.)* For $|V|\ge2$, the pairs that must be edited for every phylogenetic tree on $V$ are exactly $U^*(\vec G)=\{(x,y)\notin E:\ x\ne y,\ V[\sigma(y)]=\{y\}\}$: missing arcs into a gene that is the only one of its species.

*(3)* *(Top-down editing.)* Recursively choose a partition of the current vertex set, apply the edits $U(\vec G^*[V'],\mathscr{V})$, and recurse into each part. The output graph equals $\vec G(T,\sigma)$ for the tree $T$ built from the partitions, so it is a BMG, and its edit cost is the sum of the UR-costs of the chosen partitions (edit sets of different steps are disjoint).

*(4)* *(Consistency.)* The algorithm leaves every BMG unchanged if at each step it picks either a partition of minimal UR-cost, or, when the Aho graph of the informative triples is disconnected with zero-cost component partition, that component partition.

## Expansion

Whether $x$ in part $V_i$ has $y$ outside $V_i$ as a best match is decided at the root: if $V_i$ already contains a gene of color $\sigma(y)$, the last common ancestor inside $V_i$ is closer, so the arc must go ($U_1$); if not, every gene of that color is equally reachable only through the root, so the arc must exist ($U_2$). Inside a part, a gene that is the unique representative of its color in $V_i$ is a best match of every other gene of $V_i$ ($U_3$). Since every tree has some root partition, intersecting over all partitions leaves only the edits that no tree can avoid. Practical variants choose the partition heuristically; in the benchmarks, community-detection partitioning performed best.

## Sources

- David Schaller, Manuela Geiß, Marc Hellmuth and Peter F. Stadler, "Heuristic Algorithms for Best Match Graph Editing", arXiv:2103.07280 (2021), Definition 8, Lemma 1, Corollary 1 and Theorems 1–3 (Section 5), <https://doi.org/10.48550/arXiv.2103.07280>.
