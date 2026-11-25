# Fischer's determinant inequality

Let $A$ be a real $m \times m$ matrix, $B$ a real $m \times n$ matrix and $D$ a real $n \times n$ matrix such that the block matrix

$$M = \begin{pmatrix} A & B \\ B^{\mathsf T} & D \end{pmatrix}$$

is positive semidefinite. Then $\det M \le \det A \cdot \det D$.

## Idea

Removing the off-diagonal blocks of a positive semidefinite matrix can only increase its determinant. When $A$ is invertible, $\det M = \det A \cdot \det(D - B^{\mathsf T} A^{-1} B)$, and the Schur complement $D - B^{\mathsf T} A^{-1} B$ is positive semidefinite and lies below $D$ in the positive semidefinite order, so its determinant is at most $\det D$ by monotonicity of the determinant. Equality holds, for positive definite diagonal blocks, exactly when $B = 0$. Applied repeatedly to $1 \times 1$ diagonal blocks, Fischer's inequality gives Hadamard's inequality $\det M \le \prod_i M_{ii}$.

## Statements

- [Fischer's determinant inequality](fischer-det-from-blocks-le.md)
- [Equality case of Fischer's inequality](fischer-det-from-blocks-eq-iff.md): the equality case
- [Monotonicity of the determinant for real positive semidefinite matrices: $\det S \le \det D$ when $S \succeq 0$ and $D - S \succeq 0$](det-le-det-of-pos-semidef-le.md): monotonicity of the determinant on the positive semidefinite cone, used in the proof
- [Determinant at least one when W minus identity is positive semidefinite](one-le-det-of-pos-semidef-sub-one.md): a determinant bound used in the proof
