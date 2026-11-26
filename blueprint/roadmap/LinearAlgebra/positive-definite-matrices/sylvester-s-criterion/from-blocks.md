# Positive definiteness of a block matrix via the Schur complement

Let $n \in \mathbb{N}$, let $B$ be a real symmetric positive definite $n \times n$ matrix, let
$u \in \mathbb{R}^n$ be a column vector and let $d \in \mathbb{R}$. If the Schur complement
$d - u^{\mathsf{T}} B^{-1} u$ is positive, then the symmetric $(n+1) \times (n+1)$ block matrix

$$\begin{pmatrix} B & u \\ u^{\mathsf{T}} & d \end{pmatrix}$$

is positive definite. This is the induction step of Sylvester's criterion, with a $1 \times 1$
bottom-right block.

The off-diagonal blocks must be transposes of each other: the matrix
$\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ has a positive top-left entry and a positive Schur
complement but is not symmetric, hence not positive definite.
