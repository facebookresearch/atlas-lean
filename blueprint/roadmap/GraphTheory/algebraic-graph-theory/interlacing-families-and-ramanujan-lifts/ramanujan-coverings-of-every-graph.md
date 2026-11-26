# Hall-Puder-Sawin: Ramanujan coverings of every degree

Let $G$ be a finite connected loopless graph (multiple edges allowed) and $\rho$ the spectral radius of its universal cover. For every $r \ge 2$, $G$ has an $r$-sheeted covering $\hat G$ whose **new** eigenvalues, those not inherited from $G$, are all at most $\rho$; that is, $G$ has a one-sided Ramanujan $r$-covering. The loopless hypothesis can be replaced by regularity, but irregular graphs with loops are not covered. Since a finite graph is bipartite exactly when its spectrum is symmetric and every covering of a bipartite graph is bipartite, every connected bipartite graph has an $r$-covering whose new eigenvalues lie in $[-\rho, \rho]$. In particular, every $d$-regular bipartite Ramanujan graph has $d$-regular bipartite Ramanujan $r$-coverings for every $r$, generalizing the case $r = 2$ of Marcus-Spielman-Srivastava.

## Proof sketch

An $r$-covering is given by a permutation $\sigma_e \in S_r$ on each oriented edge, and its adjacency spectrum splits into the spectrum of $G$ (the old eigenvalues) and that of the matrix of the standard $(r-1)$-dimensional representation of $S_r$ applied to the labelling (the new eigenvalues). Only this new-spectrum factor, the characteristic polynomial of the covering divided by that of $G$, is bounded; the old part contains the eigenvalues of $G$ itself, which can exceed $\rho$. Because the exterior powers of the standard representation are irreducible and pairwise non-isomorphic, the expected new-spectrum polynomial over uniform random labellings equals the $(r-1)$-matching polynomial of $G$, a generating function of multi-matchings, which for loopless $G$ is real-rooted with all roots in $[-\rho, \rho]$. Because transpositions act as pseudo-reflections, the new-spectrum polynomials form an interlacing family, so some covering has largest new eigenvalue at most the largest root of the expectation.

## Depends on

- [Marcus-Spielman-Srivastava: every graph has a one-sided Ramanujan two-lift](every-bipartite-graph-has-a-ramanujan-two-lift.md)
- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)

## Proof depends on

- [Heilmann-Lieb theorem: real roots of the matching polynomial](heilmann-lieb-theorem.md)

## Sources

- Chris Hall, Doron Puder, William F. Sawin, "Ramanujan coverings of graphs", Advances in Mathematics 323 (2018); arXiv:1506.02335 (Theorems 1.2, 1.8, 1.10 and 2.7, Corollary 1.3, Proposition 2.3).
