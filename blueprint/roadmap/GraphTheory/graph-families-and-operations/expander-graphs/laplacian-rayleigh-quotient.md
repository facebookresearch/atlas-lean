# Laplacian Rayleigh quotient of a spectral expander

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector. For every $x$ orthogonal to the constant vector,

$$x^{\mathsf T} L x \ge d(1 - \lambda)\, x^{\mathsf T} x,$$

where $L = D - A$ is the Laplacian of $G$. Equivalently, for $N \ge 2$, the second-smallest Laplacian eigenvalue is at least $d(1 - \lambda)$. The proof: $x^{\mathsf T} L x = d\, x^{\mathsf T} x - x^{\mathsf T} A x$ and $x^{\mathsf T} A x \le \lVert x\rVert\, \lVert A x\rVert \le d\lambda \lVert x\rVert^2$.

## Background

- [Graph Laplacian as a multigraph Laplacian](../../algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/laplacian-dart-eq-lap-matrix.md): identifies
  the Laplacian $D - A$ of a simple graph with the weighted Laplacian of its dart multigraph, so
  this bound feeds the Laplacian results of the Cheeger topic.
- [Spectral expander](is-spectral-expander.md): the spectral bound $\lVert A x\rVert \le d\lambda \lVert x\rVert$ used in the proof.
