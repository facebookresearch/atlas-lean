# Schur's theorem on diagonals of self-adjoint operators

Let $E$ be a complex inner product
space of finite dimension $n$, let $T : E \to E$ be a linear operator that is symmetric, that is,
$\langle T x, y \rangle = \langle x, T y \rangle$ for all $x, y \in E$, let
$\lambda_1, \dots, \lambda_n$ be the eigenvalues of $T$ listed with multiplicity, and let
$b_1, \dots, b_n$ be an orthonormal basis of $E$. Then there is a doubly stochastic real
$n \times n$ matrix $D$ such that $\operatorname{Re} \langle b_i, T b_i \rangle =
\sum_{j=1}^n D_{ij} \lambda_j$ for every $i$.

## Sources

- I. Schur, 1923, Über eine Klasse von Mittelbildungen mit Anwendungen auf die Determinantentheorie; A. Horn, Doubly Stochastic Matrices and the Diagonal of a Rotation Matrix, Amer. J. Math. 76 (1954), 620–630, DOI 10.2307/2372705. Proves `Wanted` entry `schur_diagonal_eigenvalues_doublyStochastic`.
