# The lazy graph: spectral expansion from the second eigenvalue and from edge expansion

For a $D$-regular multigraph $G$ on a finite vertex set $V$ (rotation map on $V \times L$, $D = |L| \ge 1$), the lazy graph $G_{\mathrm{lazy}}$ is the $2D$-regular multigraph obtained by adding at every vertex one self-loop for each of its edges, so its walk operator is $\frac12(I + W_G)$. With $\lambda$, $\lambda_2$ and $h$ the spectral expansion, second eigenvalue and edge expansion of a regular multigraph,

$$\lambda(G_{\mathrm{lazy}}) \le \frac{1 + \lambda_2(G)}{2} \qquad\text{and}\qquad \lambda(G_{\mathrm{lazy}}) \le 1 - \frac{h(G)^2}{4D^2}.$$

More generally, superposing $G$ with $E$ self-loops per vertex gives a $(D + E)$-regular multigraph of spectral expansion at most $(D\lambda(G) + E)/(D + E)$.

## Proof sketch

The lazy walk operator is positive semidefinite, so its spectral expansion equals its largest eigenvalue on mean-zero functions, which is $(1 + \lambda_2(G))/2$. The hard direction of Cheeger's inequality bounds $1 - \lambda_2(G) \ge h(G)^2/(2D^2)$, giving the second bound. The superposition bound is the triangle inequality for the weighted average of walk operators.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Cheeger's inequality, hard direction](../../algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/exists-threshold-cut-le-sqrt.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM, 2007.
