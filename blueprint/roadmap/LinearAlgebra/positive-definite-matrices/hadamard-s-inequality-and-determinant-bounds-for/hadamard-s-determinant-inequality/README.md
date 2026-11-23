# Hadamard's determinant inequality

For every $n \times n$ complex matrix $A = (a_{ij})$,

$$|\det A| \le \prod_{i=1}^{n} \Big(\sum_{j=1}^{n} |a_{ij}|^2\Big)^{1/2}:$$

the absolute value of the determinant is at most the product of the Euclidean lengths of the rows.

## Idea

For a real matrix, $|\det A|$ is the volume of the parallelepiped spanned by the rows, and a parallelepiped with given edge lengths has the largest volume when its edges are orthogonal. For complex rows this picture fails: in $\mathbb C^2$, seen as $\mathbb R^4$, the rows $(1, 0)$ and $(i, 0)$ span a parallelogram of area $1$, but their determinant is $0$. The proof uses instead $|\det A|^2 = \det(AA^*)$, the determinant of the Hermitian Gram matrix of the rows, and orthogonalizes the rows by complex Gram–Schmidt, which does not change the determinant and can only shorten them. For a positive semidefinite matrix $A$, writing $A = CC^*$ and applying the inequality to $C$ gives $\det A \le \prod_i a_{ii}$, since $a_{ii}$ is the squared length of the $i$-th row of $C$. For $n \ge 1$, the arithmetic–geometric mean inequality for the diagonal entries then gives $(\det A)^{1/n} \le \operatorname{tr}(A)/n$, with equality only for the nonnegative multiples of the identity. Matrices with entries $\pm 1$ attaining Hadamard's bound $n^{n/2}$ are the Hadamard matrices.

## Statements

- [Hadamard's determinant inequality](hadamard-determinant-inequality.md)
- [Hadamard's inequality for positive semidefinite matrices](det-re-le-prod-diag-re.md): for positive semidefinite matrices: at most the product of the diagonal entries
- [AM–GM inequality for the determinant of a positive semidefinite matrix](geom-mean-det-le-trace-div.md): a consequence of the positive semidefinite form and the arithmetic–geometric mean inequality for the diagonal entries: $(\det A)^{1/n} \le \operatorname{tr}(A)/n$ for $n \ge 1$
- [AM–GM inequality for the determinant of a positive semidefinite matrix, power form](det-re-le-pow-trace-div.md): the same bound in power form
- [Equality in the AM–GM bound for the determinant](amgm-eq-iff.md): equality in that bound
