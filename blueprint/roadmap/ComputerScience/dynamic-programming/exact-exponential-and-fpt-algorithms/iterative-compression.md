# Iterative compression

**Iterative compression** solves a minimization problem on graphs whose solutions are vertex subsets closed under taking induced subgraphs (if $X$ is a solution for $G$ then $X \cap V'$ is a solution for $G[V']$). Order the vertices $v_1, \dots, v_n$ and maintain a solution $X_i$ of size at most $k$ for $G_i = G[\{v_1, \dots, v_i\}]$. Then $X_i \cup \{v_{i+1}\}$ is a solution of size at most $k+1$ for $G_{i+1}$; the **compression step** either turns a size-$(k+1)$ solution into one of size at most $k$ or certifies that none exists, in which case $G$ has none either.

## Depends on

- [Odd cycle transversal instances](../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/odd-cycle-transversal/odd-cycle-transversal-instance.md)

## Sources

- B. Reed, K. Smith and A. Vetta, "Finding Odd Cycle Transversals", Operations Research Letters 32(4), 2004.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
