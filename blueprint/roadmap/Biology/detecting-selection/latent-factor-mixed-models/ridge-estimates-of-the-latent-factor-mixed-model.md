# Ridge estimates of the latent factor mixed model

Let $Y \in \mathbb{R}^{n \times p}$ be a response matrix ($n$ individuals, $p$ markers), $X \in \mathbb{R}^{n \times d}$ a matrix of primary (environmental) variables with $d < n$, and consider the latent factor mixed model

$$Y \;=\; XB^{\top} + W + E, \qquad \operatorname{rank} W \le K,$$

with effect sizes $B \in \mathbb{R}^{p \times d}$, a latent confounder matrix $W = UV^{\top}$ ($U \in \mathbb{R}^{n\times K}$ scores, $V \in \mathbb{R}^{p\times K}$ loadings) and residual $E$. For $\lambda > 0$ the ridge estimates minimize

$$\mathcal L(W, B) \;=\; \|Y - W - XB^{\top}\|_F^2 + \lambda\,\|B\|_F^2 \quad \text{over } \operatorname{rank} W \le K .$$

Let $X = Q\Sigma R^{\top}$ be a full singular value decomposition with $Q \in O(n)$ and singular values $\sigma_1, \dots, \sigma_d$, and let

$$D_\lambda \;=\; \operatorname{diag}\Bigl(\sqrt{\tfrac{\lambda}{\lambda + \sigma_1^2}}, \dots, \sqrt{\tfrac{\lambda}{\lambda + \sigma_d^2}}, 1, \dots, 1\Bigr) \in \mathbb{R}^{n \times n}.$$

Then a minimizer is

$$\widehat W \;=\; Q\,D_\lambda^{-1}\,\operatorname{svd}_K\!\bigl(D_\lambda Q^{\top} Y\bigr), \qquad \widehat B^{\top} \;=\; (X^{\top}X + \lambda I_d)^{-1} X^{\top}\bigl(Y - \widehat W\bigr),$$

where $\operatorname{svd}_K$ is the best rank-$K$ approximation in Frobenius norm. It is unique whenever the $K$-th and $(K+1)$-th singular values of $D_\lambda Q^\top Y$ differ. At $\lambda = 0$ the problem has infinitely many solutions, among them principal-component correction followed by regression. Association of marker $j$ is then tested by regressing $y_j$ on $X$ and the estimated scores $\widehat U$, using a Student $t$ test with $n - K - 1$ degrees of freedom for $d = 1$, followed by empirical-null calibration.

## Depends on

- [Real singular value decomposition](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md)
- [Truncated singular value decomposition](../../../Probability/linear-models-multivariate/principal-component-analysis/trunc-svd.md)

## Proof depends on

- [Eckart–Young, best-approximation form](../../../Probability/linear-models-multivariate/principal-component-analysis/is-least-frobenius-sub-sq.md)

## Expansion

For fixed $W$, set $Z = Y - W$. Minimizing over $B$ is ridge regression with solution $B^{\top} = (X^{\top}X + \lambda I)^{-1}X^{\top}Z$ and minimum value $\operatorname{tr}\bigl(Z^{\top}(I - X(X^{\top}X + \lambda I)^{-1}X^{\top})Z\bigr)$. In the singular basis, $I - X(X^{\top}X + \lambda I)^{-1}X^{\top} = Q\,\operatorname{diag}\bigl(\tfrac{\lambda}{\lambda + \sigma_j^2}, 1, \dots, 1\bigr)Q^{\top} = QD_\lambda^2 Q^{\top}$, so the profile loss is $\|D_\lambda Q^{\top}(Y - W)\|_F^2$. Because $\lambda > 0$, $D_\lambda Q^{\top}$ is invertible, so $M = D_\lambda Q^{\top}W$ ranges over all matrices of rank at most $K$. The Eckart–Young theorem then gives $M = \operatorname{svd}_K(D_\lambda Q^{\top}Y)$, unique under the stated gap condition, and $W = QD_\lambda^{-1}M$. The cost is dominated by a truncated SVD, $O(npK)$ or $O(np\log K)$ with random projections, plus $O(n^2p)$ for $Q^\top Y$. When $n \ll p$ this costs about as much as two SVDs of the response matrix; in simulations the method was several orders of magnitude faster than its Bayesian predecessor without loss of power, and it outperformed fast approaches based on principal components or surrogate variables.

## Sources

- K. Caye, B. Jumentier, J. Lepeule, O. François, "LFMM 2: fast and accurate inference of gene-environment associations in genome-wide studies", *Molecular Biology and Evolution* 36(4) (2019) 852–860, New Approaches, "L2-Regularized Least-Squares Problem", "Ridge Estimates" (Equations (2)–(4)) and "Statistical Tests" (Equation (5)), <https://doi.org/10.1093/molbev/msz008> (PMC6659841).
