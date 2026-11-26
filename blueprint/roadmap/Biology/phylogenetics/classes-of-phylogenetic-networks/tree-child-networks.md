# Tree-child networks

Let $X$ be a non-empty finite set of taxa. If $|X| = 1$, the only **rooted binary phylogenetic network** on $X$ is the single vertex labelled by the element of $X$, which is both root and leaf. If $|X| \ge 2$, a **rooted binary phylogenetic network** on $X$ is a rooted directed acyclic graph $N = (V, E)$ without parallel arcs such that the root has in-degree $0$ and out-degree $2$; the vertices of out-degree $0$ have in-degree $1$ and form the leaf set $X$; every other vertex is either a *tree vertex* (in-degree $1$, out-degree $2$) or a *reticulation* (in-degree $2$, out-degree $1$). A vertex $v$ is *visible* if some leaf $x$ has the property that every directed path from the root to $x$ passes through $v$.

**Definition.** $N$ is **tree-child** if every non-leaf vertex has a child that is a tree vertex or a leaf.

**Proposition.** For a rooted binary phylogenetic network $N$ the following are equivalent:

1. $N$ is tree-child;
2. (*tree-path property*) every vertex $v$ has a directed path to a leaf on which every vertex other than $v$ and the leaf is a tree vertex;
3. no tree vertex has two reticulation children and no reticulation has a reticulation child.

Moreover, every vertex of a tree-child network is visible.

## Expansion

(1 ⇒ 2): from $v$ repeatedly step to a child that is a tree vertex or a leaf; acyclicity forces the walk to end at a leaf. (2 ⇒ 1): the second vertex of such a path is a tree-vertex or leaf child of $v$. (1 ⇔ 3): a tree vertex has two children and a reticulation one child, so "some child is not a reticulation" fails exactly in the two forbidden configurations. Visibility: the tree path from $v$ to a leaf $x$ uses only vertices of in-degree one after $v$, so any root-to-$x$ path must enter that path through $v$. Biologically the condition says every ancestral taxon has descendants that persisted by vertical descent alone, not only through hybrids; tree-child networks that are also time consistent are the TCTC networks, and tree-child networks without shortcuts are the *normal* networks.

## Sources

- S. Kong, J. C. Pons, L. Kubatko and K. Wicke, "Classes of explicit phylogenetic networks and their biological and mathematical significance", Journal of Mathematical Biology 84 (2022), 47, <https://doi.org/10.1007/s00285-022-01746-y>. Definition 1 (Section 2) and Section 3.1, "Tree-child networks".
- G. Cardona, F. Rosselló and G. Valiente, "Comparison of tree-child phylogenetic networks", IEEE/ACM Transactions on Computational Biology and Bioinformatics 6 (2009), 552–569, <https://doi.org/10.1109/TCBB.2007.70270>.
