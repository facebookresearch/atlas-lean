# Constant-degree expanders exist on every finite vertex set

Every finite set $V$ carries a $120$-regular multigraph with spectral expansion at most $1 - 1/360000$; when $|V| \ge 2$ its edge expansion is at least $1/6000$. Specifically, there are thirty permutations of $V$ such that every set $S$ with $|S| \le |V|/2$ has at least $|S|/10$ of its points moved out of $S$ by one of them; their $60$-regular permutation multigraph has edge expansion at least $1/5$, and its lazy graph has the stated spectral bound. The degree and the gap do not depend on $|V|$; the construction is not explicit.

## Proof sketch

Count permutations: a fixed $S$ of size $s \le n/2$ is failed by a uniform permutation (fewer than $s/10$ points leave) with probability at most $3^s (s/2n)^k$ with $k \ge 9s/10$, so thirty independent permutations all fail it with probability at most $3^{30s}(s/2n)^{27s}$; summing over all $S$ gives total probability below one. Dart counting in the permutation multigraph gives edge expansion $1/5$, and the lazy Cheeger bound $1 - h^2/(4D^2)$ gives $1 - 1/360000$.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Regular multigraph of a family of permutations (Schreier-type graph)](../expander-graph-operations/permutation-multigraph.md)
- [The lazy graph: spectral expansion from the second eigenvalue and from edge expansion](../expander-graph-operations/lazy-graph-spectral-bounds.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM, 2007.
- E. Ben-Sasson, A. Wigderson, "Short Proofs Are Narrow - Resolution Made Simple", Journal of the ACM, 2001.
