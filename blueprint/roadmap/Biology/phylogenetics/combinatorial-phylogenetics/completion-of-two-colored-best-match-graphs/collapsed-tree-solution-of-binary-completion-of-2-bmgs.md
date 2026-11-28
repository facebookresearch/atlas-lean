# Collapsed-tree solution of the binary-explainable completion of 2-colored best match graphs

**Setting.** A best match graph (BMG) of a leaf-colored tree $(T,\sigma)$ has an arc $(x,y)$ when $y$ is a closest relative of $x$ of color $\sigma(y)\ne\sigma(x)$. A BMG is *binary-explainable* (beBMG) if some binary tree explains it, equivalently if it has no induced *hourglass* $[xy\,\Join\,x'y']$: four vertices with $\sigma(x)=\sigma(x')\ne\sigma(y)=\sigma(y')$, bidirectional arcs $x\leftrightarrow y$ and $x'\leftrightarrow y'$, arcs $(x,y'),(y,x')$, and non-arcs $(y',x),(x',y)$. A *2-BMG* uses two colors. In the LRT of a 2-BMG, $(x,y)$ is an arc if and only if $\sigma(x)\ne\sigma(y)$ and $y$ lies below the parent of $x$.

For a tree $(T,\sigma)$ with two leaf colors, the *collapsed tree* $(T^*,\sigma)$ contracts all inner edges inside $T(u)$ for every inner vertex $u$ whose children that are leaves (its *support leaves*) carry both colors. $T^*$ is unique, computable in $O(|V(T)|)$ time, and idempotent ($T^{**}=T^*$).

**Theorem.** Let $(G,\sigma)$ be a 2-BMG with LRT $(T,\sigma)$.

*(1)* In any completion of a BMG to a beBMG, every induced hourglass $[xy\,\Join\,x'y']$ receives both missing arcs $(x',y)$ and $(y',x)$.

*(2)* The minimum-cardinality arc completion of $(G,\sigma)$ to a binary-explainable 2-BMG is unique and equals

$$F=E\big(G(T^*,\sigma)\big)\setminus E(G).$$

*(3)* This completion problem with a 2-BMG as input is solvable in $O(|V|+|E|\log^2|V|)$ time, whereas the same completion problem for arbitrary properly 2-colored input digraphs is NP-complete.

*(4)* A 2-colored least resolved tree is the LRT of a binary-explainable 2-BMG if and only if it is a collapsed tree.

## Expansion

Item 1: adding only one of the two missing arcs would create a forbidden F2 subgraph of 2-BMGs. Because $T^*$ arises from the LRT by contracting inner edges, it is again least resolved and its BMG contains $G$; the hourglass criterion in tree form (no inner vertex with three children carrying color sets $\{r\}$, $\{r,s\}$, $\{s\}$) fails for $T^*$ since every vertex with bichromatic support leaves has been flattened, so $G(T^*,\sigma)$ is binary-explainable. Minimality and uniqueness come from showing that any beBMG completion must already contain all arcs forced by collapsing such subtrees. The running time is dominated by computing the LRT of the input 2-BMG. Best match graphs are the usual first step of graph-based orthology inference, so this gives an exact, efficient noise-correction step toward binary gene trees in the two-species case.

## Depends on

- [Edge contraction preserves least resolved trees of best match graphs](edge-contraction-preserves-least-resolved-trees.md)

## Sources

- D. Schaller, M. Geiß, M. Hellmuth, P. F. Stadler, "Arc-completion of 2-colored best match graphs to binary-explainable best match graphs", arXiv:2103.06665 (2021), Definitions 4, 5, 7 and 8, Proposition 3, Lemmas 1, 2, 3 and 4, Corollaries 3 and 4, Theorem 2, Corollaries 5 and 6, <https://doi.org/10.48550/arXiv.2103.06665>.
