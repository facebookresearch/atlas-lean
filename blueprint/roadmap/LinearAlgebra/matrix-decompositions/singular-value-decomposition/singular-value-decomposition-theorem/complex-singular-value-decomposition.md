# Singular value decomposition of a complex matrix

Let $m, n \in \mathbb{N}$. Every complex $m \times n$ matrix $A$ factors as $A = U \Sigma V^*$, where
$U$ is a unitary $m \times m$ matrix, $V$ is a unitary $n \times n$ matrix, and $\Sigma$ is the
$m \times n$ matrix with $\Sigma_{jj} = \sigma_j$ and all other entries $0$, for real numbers
$\sigma_1, \dots, \sigma_n \ge 0$ with $\sigma_j = 0$ whenever $j > m$.

Proof: Apply the spectral theorem to `AᴴA`, normalize the images of the
eigenvectors with positive eigenvalues, and extend them to an orthonormal basis
of the codomain, as in the proof of S. Axler, Linear Algebra Done Right,
4th ed., 7.70, and the matrix form that follows it (Section 7E).

## Sources

- S. Axler, Linear Algebra Done Right, 4th ed., Section 7E; G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins University Press (2013), Theorem 2.4.1.
