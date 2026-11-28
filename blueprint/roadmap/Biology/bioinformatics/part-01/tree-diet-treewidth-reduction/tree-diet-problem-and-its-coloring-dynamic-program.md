# Tree-diet problem and its coloring dynamic program

**Definitions.** Let $G=(V,E)$ be a graph and $\mathcal T$ a tree-decomposition of $G$ of width $w(\mathcal T)=tw$ (maximum bag size minus one). A *tree-diet* of $\mathcal T$ is any tree-decomposition $\mathcal T'$ obtained by deleting vertices from bags of $\mathcal T$ (keeping each vertex's bags connected); it is a $d$-tree-diet if $w(\mathcal T')\le w(\mathcal T)-d$. An edge $(u,v)\in E$ is *lost* if no bag of $\mathcal T'$ contains both $u$ and $v$; $\mathcal T'$ is then a tree-decomposition of $G$ minus the lost edges.

**Problem (Tree-Diet).** Given $G$, a tree-decomposition $\mathcal T$ of width $tw$ and a target $tw'<tw$, find a $(tw-tw')$-tree-diet of $\mathcal T$ losing the minimum number of edges. (Path-Diet and Binary-Tree-Diet restrict $\mathcal T$ to a path or a binary tree.)

**Coloring reformulation.** Color the vertices of each bag green, orange or red by the rules: a vertex absent from the parent bag is green or orange; a green vertex stays green or turns red in a child; a red vertex stays red; an orange vertex is orange or green in exactly one child containing it (unless no child contains it) and red in all others. Kept occurrences are the green ones. Tree-Diet is equivalent to finding a coloring of this kind with at most $tw'+1$ green vertices per bag that maximizes the number of *realizable* edges, those whose endpoints are green together in some bag.

**Theorem.** Tree-Diet can be solved in $O(\Delta^{tw+2}\cdot 6^{tw}\cdot n)$ time and $O(3^{tw}\cdot n)$ space, where $\Delta$ is the maximum number of children of a bag. On binary tree-decompositions this is an FPT algorithm in $O(12^{tw}n)$ time.

## Expansion

The dynamic program has one cell $c(X_i,f)$ per bag $X_i$ and coloring $f$ of $X_i$, equal to the maximum number of realizable edges counted strictly below $X_i$ (or $-\infty$ if $f$ keeps more than $tw'+1$ green vertices). Each realizable edge is counted exactly once, at the root of the subtree where both endpoints are green, so the recurrence sums over children: for each child $Y_j$ it maximizes over child colorings compatible with $f$ and with a map $m$ assigning each orange vertex of $X_i$ that occurs in at least one child to the one child that keeps it alive (an orange vertex occurring in no child needs no child assignment). With $3^{|X_i|}$ colorings per bag and $\Delta^{\#\text{orange}}$ choices of $m$, the stated bounds follow, and the optimum is read at the empty root bag. Orange encodes "kept in exactly one downward branch", which is all a connected subtree of bags can do once it is cut.

## Sources

- B. Marchand, Y. Ponty, L. Bulteau, "Tree diet: reducing the treewidth to unlock FPT algorithms in RNA bioinformatics", *Algorithms for Molecular Biology* 17:8 (2022), Definition 1, Proposition 1, Lemma 1, Theorems 6 and 7, <https://doi.org/10.1186/s13015-022-00213-z>, PMCID: PMC8976393.
