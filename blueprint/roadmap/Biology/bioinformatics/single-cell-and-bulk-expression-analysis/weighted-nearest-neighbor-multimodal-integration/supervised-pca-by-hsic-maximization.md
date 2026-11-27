# Supervised principal component analysis by HSIC maximization

Let $X \in \mathbb{R}^{p \times n}$ hold $p$ features (genes) for $n$ cells, let $L \in \mathbb{R}^{n \times n}$ be a symmetric cell–cell kernel encoding a response (for example similarities from a multimodal neighbour graph), and let $H = I_n - \frac{1}{n} e e^{\top}$ be the centring matrix, $e = (1, \dots, 1)^{\top}$. The Hilbert–Schmidt Independence Criterion of two $n \times n$ kernels is

$$\mathrm{HSIC}(K, L) = \frac{1}{(n-1)^2} \operatorname{tr}(K H L H).$$

For a projection $U \in \mathbb{R}^{p \times d}$ with $U^{\top} U = I_d$, the linear kernel of the projected data is $K = (U^{\top} X)^{\top} U^{\top} X$, and

$$\mathrm{HSIC}(K, L) = \frac{1}{(n-1)^2} \operatorname{tr}\!\left(U^{\top} X H L H X^{\top} U\right).$$

**Theorem.** Let $\lambda_1 \ge \dots \ge \lambda_p$ be the eigenvalues of the symmetric matrix $Q = X H L H X^{\top}$ with orthonormal eigenvectors $u_1, \dots, u_p$. Then

$$\max_{U^{\top} U = I_d} \operatorname{tr}(U^{\top} Q U) = \sum_{j=1}^{d} \lambda_j,$$

attained at $U = [u_1, \dots, u_d]$. The maximizer is unique up to right multiplication by an orthogonal $d \times d$ matrix when $\lambda_d > \lambda_{d+1}$. If $L$ is positive semidefinite, so is $Q$, and all $\lambda_j \ge 0$.

The columns of $U$ are gene loadings of components that maximally depend, in the HSIC sense, on the structure in $L$.

## Proof sketch

Since $\operatorname{tr}(KHLH)$ with $K = X^{\top} U U^{\top} X$ equals $\operatorname{tr}(U^{\top} X H L H X^{\top} U)$ by cyclicity of the trace, the problem is a trace maximization over the Stiefel manifold, solved by Ky Fan's maximum principle. With $L = I_n$ the matrix $Q$ is $(n-1)$ times the sample covariance of the features and the procedure reduces to ordinary PCA, so supervision enters only through $L$. Positive semidefiniteness of $Q$ follows from $Q = (X H) L (X H)^{\top}$ because $H$ is symmetric. In multimodal reference mapping, $L$ is built from the weighted nearest neighbour graph, so the transcriptomic components are chosen to reproduce structure defined jointly by RNA and protein.

## Sources

- Y. Hao, S. Hao, E. Andersen-Nissen, et al., "Integrated analysis of multimodal single-cell data", Cell 184 (2021) 3573–3587, STAR Methods section "Supervised principal component analysis for multimodal data", <https://doi.org/10.1016/j.cell.2021.04.048> (PMC8238499).
- E. Barshan, A. Ghodsi, Z. Azimifar, M. Zolghadri Jahromi, "Supervised principal component analysis: visualization, classification and regression on subspaces and submanifolds", Pattern Recognition 44 (2011) 1357–1371, <https://doi.org/10.1016/j.patcog.2010.12.015>.
