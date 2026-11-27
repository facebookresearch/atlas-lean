# Minkowski's determinant inequality

Let $n \ge 1$ and let $A$ and $B$ be positive semidefinite complex $n \times n$ matrices. Then

$$(\det A)^{1/n} + (\det B)^{1/n} \le \bigl(\det(A + B)\bigr)^{1/n},$$

where the determinants are nonnegative real numbers and $t^{1/n}$ is the real $n$-th root.

## Idea

The inequality says that $A \mapsto (\det A)^{1/n}$ is superadditive, and, being homogeneous of degree one, concave on the positive semidefinite cone. For diagonal matrices it is the inequality $\prod (a_i + b_i)^{1/n} \ge \prod a_i^{1/n} + \prod b_i^{1/n}$, which follows from the arithmetic–geometric mean inequality; the general case reduces to it by simultaneously diagonalizing $A$ and $B$ by congruence when $A$ is positive definite. A consequence is the monotonicity of the determinant: $\det B \le \det(A + B)$. The inequality is the matrix counterpart of the Brunn–Minkowski inequality for volumes.

## Statements

- [Minkowski's determinant inequality](minkowski-det.md)
- [Adding a positive semidefinite matrix does not decrease the determinant: $\det B \le \det(A + B)$](det-le-det-add.md): consequence: the determinant is monotone on the positive semidefinite cone
