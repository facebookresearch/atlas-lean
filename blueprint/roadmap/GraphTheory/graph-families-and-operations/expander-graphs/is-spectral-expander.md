# Spectral expander

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, $d$ a natural number and $\lambda$ a real number. $G$ is a spectral expander of degree $d$ with parameter $\lambda$ (an $(N, d, \lambda)$-graph) when it is $d$-regular, $\lambda \ge 0$, and

$$\lVert A x\rVert \le d\lambda\, \lVert x\rVert \quad \text{for every } x \text{ orthogonal to the constant vector},$$

that is, its random-walk matrix $A/d$ satisfies $\lVert (A/d) x\rVert \le \lambda \lVert x\rVert$ on that complement when $d \ge 1$ (S. Vadhan, *Pseudorandomness* (2012), Definition 4.5 with $\lambda = 1 - \gamma$; O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Definition 1.1).

For a $d$-regular undirected graph with $d \ge 1$ and $N \ge 1$ vertices the random-walk matrix $A/d$ is symmetric with the constant vector as an eigenvector, so it preserves the orthogonal complement of the constants, and the smallest admissible $\lambda$ is the largest absolute value of an eigenvalue of $A/d$ on that complement (eigenvalues counted with multiplicity, the constant eigenvector removed; Reingold, Vadhan and Wigderson, Definition 2.2). For a disconnected graph the eigenvalue $1$ occurs again on the complement, so $\lambda \ge 1$. This two-sided measure differs from the one-sided second eigenvalue $\lambda_2$, and from the bipartite convention of [Bipartite Ramanujan graphs of every degree](exists-bipartite-ramanujan.md), which excludes both trivial eigenvalues $\pm d$.

## Background

- [Graph Laplacians and Cheeger's inequality](../../algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/README.md):
  for a $d$-regular graph the Laplacian is $d I - A$, so for $N \ge 2$ a bound on $\lambda$ bounds the second-smallest
  Laplacian eigenvalue $\lambda_2(L) \ge d(1 - \lambda)$, the quantity in Cheeger's inequality; the Rayleigh-quotient
  form is proved in [Laplacian Rayleigh quotient of a spectral expander](laplacian-rayleigh-quotient.md).
