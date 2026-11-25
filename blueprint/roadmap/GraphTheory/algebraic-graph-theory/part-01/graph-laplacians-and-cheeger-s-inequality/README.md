# Graph Laplacians and Cheeger's inequality

The weighted Laplacian $L = B \operatorname{diag}(w) B^{\mathsf T}$ of a finite multigraph and its quadratic form $x^{\mathsf T} L x = \sum_e w_e (x(a) - x(b))^2$, following D. A. Spielman, *Spectral and Algebraic Graph Theory* (Chapters 3, 20 and 21). For nonnegative weights the Laplacian is positive semidefinite, and the Loewner order on Laplacians comes from linear algebra; the Courant–Fischer theorem turns the second-smallest eigenvalue $\lambda_2$ into a minimum of Rayleigh quotients over vectors orthogonal to the constants, which gives connectivity (for positive weights on a loopless multigraph with at least two vertices, $\lambda_2 > 0$ iff the multigraph is connected) and the easy direction of Cheeger's inequality. The hard direction, for conductance, is in the conductance topic. Spectral clustering and Laplacian eigenmaps in machine learning use exactly these eigenvectors.

- [Weighted Laplacian of a multigraph](laplacian.md)
- [The weighted Laplacian is symmetric](laplacian-transpose.md)
- [The weighted Laplacian is additive in the weights](laplacian-add.md)
- [The weighted Laplacian is additive in the weights: subtraction](laplacian-sub.md)
- [Entries of the weighted Laplacian](laplacian-apply.md)
- [Graph Laplacian as a multigraph Laplacian](laplacian-dart-eq-lap-matrix.md)
- [Laplacian quadratic form](dot-product-mul-vec-laplacian.md)
- [Constants are in the kernel of the Laplacian](laplacian-mul-vec-one.md)
- [The Laplacian of nonnegative weights is positive semidefinite](pos-semidef-laplacian.md)
- [Loewner monotonicity in the weights](pos-semidef-laplacian-sub-of-le.md)
- [Kernel of the Laplacian](laplacian-mul-vec-eq-zero-iff.md)
- [Rank of the Laplacian plus number of components](rank-laplacian-add-card-connected-compon.md)
- [Indicator vector of a vertex set](indicator.md)
- [Quadratic form of an indicator is the cut weight](indicator-dot-product-mul-vec-laplacian.md)
- [Easy direction of Cheeger's inequality](mul-card-mul-card-compl-le-of-forall.md)
- [Graph of positive-weight arcs](positive-arc-graph.md)
- [Zero energy forces equal potentials along positive-weight walks](eq-of-energy-eq-zero.md)
- [Kernel of the weighted Laplacian of an arc network with nonnegative weights](weighted-laplacian-mul-vec-eq-zero-iff.md)
- [Kernel of the weighted Laplacian of an arc network connected from a root](weighted-laplacian-mul-vec-eq-zero-iff-o.md)
- [The grounded weighted Laplacian of an arc network is positive definite](grounded-weighted-laplacian-pos-def.md)
- [The grounded weighted Laplacian of an arc network is invertible](grounded-weighted-laplacian-is-unit.md)
- [The Laplacian as a symmetric operator](is-symmetric-to-euclidean-lin-laplacian.md)
- [Algebraic connectivity](algebraic-connectivity.md)
- [$\lambda_2$ bounds the Rayleigh quotient on vectors orthogonal to the constants](algebraic-connectivity-mul-le.md)
- [Easy direction of Cheeger's inequality, eigenvalue form](algebraic-connectivity-mul-card-mul-card.md)
- [$\lambda_2 > 0$ exactly for connected multigraphs](algebraic-connectivity-pos-iff.md)
- [Laplacian eigenvalues are monotone in the Loewner order](eigenvalues-laplacian-le-of-pos-semidef.md)
- [Raising weights raises every Laplacian eigenvalue](eigenvalues-laplacian-mono.md)
- [Algebraic connectivity is monotone in the weights](algebraic-connectivity-mono.md)
- [Hall's spectral drawing is optimal](sum-eigenvalues-le-sum-quadratic-form.md)
- [With positive weights, the graph of positive arcs is the underlying graph](positive-arc-graph-eq-of-pos.md)

## Related topics

- [Oriented incidence matrices](../oriented-incidence-matrices/README.md): the matrix $B$ in $L = B \operatorname{diag}(w) B^{\mathsf T}$; its kernel and rank give those of $L$.
- [Courant–Fischer min–max theorem](../../../../Analysis/operator-theory/eigenvalue-inequalities/courant-fischer-min-max-theorem/README.md): the variational characterisation used to bound $\lambda_2$ by Rayleigh quotients.
- [Positive definite matrices and matrix inequalities](../../../../LinearAlgebra/positive-definite-matrices/README.md): Laplacians of nonnegative weights are positive semidefinite, and graphs are compared in the Loewner order.
- [Kirchhoff's matrix-tree theorem](../kirchhoff-s-matrix-tree-theorem/README.md): stated with the Laplacian $D - A$ of a simple graph, which equals the multigraph Laplacian of its darts.
- [Effective resistance and electrical networks](../effective-resistance-and-electrical-networks/README.md): the Laplacian as the operator of a resistor network: potentials, energy and effective conductance.
- [Spectral sparsification](../../part-02/spectral-sparsification/README.md): approximating a Laplacian in the Loewner order by one with few edges.
- [Expander graphs](../../../graph-families-and-operations/expander-graphs/README.md): Cheeger's inequality relates the spectral gap $\lambda_2$ to edge expansion.
- [Unsupervised learning and matrix factorization](../../../../ComputerScience/machine-learning/unsupervised-learning/README.md): spectral clustering embeds the vertices with the bottom Laplacian eigenvectors and then clusters them.
- [Gaussian graphical models](../../../../Probability/linear-models-multivariate/gaussian-graphical-models/README.md): the Leroux conditional autoregressive precision matrix $\rho L + (1 - \rho) I$ is built from a weighted graph Laplacian, with the same quadratic form.
- [Conductance and Cheeger's inequality](../../part-02/conductance-and-cheeger-s-inequality/README.md): weighted degrees, conductance and both directions of Cheeger's inequality.
