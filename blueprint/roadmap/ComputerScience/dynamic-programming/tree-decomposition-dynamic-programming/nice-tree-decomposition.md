# Nice tree decompositions

A **nice tree decomposition** of a graph $G$ is a rooted tree decomposition $(T, (B_t)_{t \in V(T)})$ in which every node $t$ is of one of four kinds: a **leaf** with $B_t = \emptyset$; an **introduce** node with one child $t'$ and $B_t = B_{t'} \cup \{v\}$ for some $v \notin B_{t'}$; a **forget** node with one child $t'$ and $B_t = B_{t'} \setminus \{v\}$ for some $v \in B_{t'}$; or a **join** node with two children $t_1, t_2$ and $B_t = B_{t_1} = B_{t_2}$; and the root bag is empty. Every tree decomposition of width $w$ with $N$ nodes can be converted into a nice one of width $w$ with $O(w N)$ nodes.

## Depends on

- [Tree-decomposition](../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)

## Sources

- T. Kloks, "Treewidth: Computations and Approximations", LNCS 842, Springer, 1994.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
