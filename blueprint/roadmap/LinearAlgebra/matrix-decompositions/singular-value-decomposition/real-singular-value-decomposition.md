# Real singular value decomposition

Let $A$ be a real $m \times n$ matrix. Then there are
orthogonal matrices $U$ of size $m \times m$ and $V$ of size $n \times n$ and real numbers
$\sigma_1, \dots, \sigma_n \ge 0$ with $\sigma_j = 0$ for every $j > m$, such that
$A = U \Sigma V^{\mathsf{T}}$, where $\Sigma$ is the $m \times n$ matrix with
$\Sigma_{jj} = \sigma_j$ for $j \le \min(m, n)$ and all other entries zero.

Proof: apply the spectral theorem to $A^{\mathsf{T}} A$, normalize the images under $A$ of the
eigenvectors with positive eigenvalues, and extend them to an orthonormal basis of
$\mathbb{R}^m$, as in the proof of S. Axler, Linear Algebra Done Right, 4th ed., 7.70, and the
matrix form that follows it (Section 7E).

## Sources

- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Iterative methods / singular value decomposition; G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins University Press (2013), Theorem 2.4.1.
