# Iterative compression

**Iterative compression** solves a vertex-deletion problem on graphs: for a fixed class $\Pi$ of graphs that is closed under taking induced subgraphs and contains the empty graph, a *solution* for $G$ is a vertex set $X$ with $G - X \in \Pi$ (for odd cycle transversal, $\Pi$ is the class of bipartite graphs), and the task is to find one of size at most $k$. Order the vertices $v_1, \dots, v_n$, let $G_i = G[\{v_1, \dots, v_i\}]$, and maintain a solution $X_i$ of size at most $k$ for $G_i$, starting from $X_0 = \emptyset$. Then $X_i \cup \{v_{i+1}\}$ is a solution of size at most $k+1$ for $G_{i+1}$; the **compression step** either turns a size-$(k+1)$ solution into one of size at most $k$ or certifies that none exists, in which case $G$ has none either (Cygan et al., Section 4.1.1).

## Proof sketch

$G_{i+1} - (X_i \cup \{v_{i+1}\}) = G_i - X_i \in \Pi$. If $X$ is a solution for $G$, then $G_{i+1} - (X \cap V(G_{i+1}))$ is an induced subgraph of $G - X$, so $X \cap V(G_{i+1})$ is a solution for $G_{i+1}$ of no larger size. The vertex-deletion form is needed: for a property such as "independent vertex cover", which is preserved under restriction to induced subgraphs, adding $v_{i+1}$ to $X_i$ can break independence.

## Depends on

- [Odd cycle transversal instances](../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/odd-cycle-transversal/odd-cycle-transversal-instance.md)

## Sources

- B. Reed, K. Smith and A. Vetta, "Finding Odd Cycle Transversals", Operations Research Letters 32(4), 2004.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
