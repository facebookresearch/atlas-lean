---
article_id: af_d29083629a30e871d6e1851b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SymmetricMatrixProperties.proposition2_symmetric_matrix
---

# Proposition 2 (Lecture 1, Section 2)

If $M$ is a symmetric $n \times n$ matrix, then: (1) If $v$ and $w$ are eigenvectors of $M$ with different eigenvalues, then $v$ and $w$ are orthogonal ($v \cdot w = 0$). (2) If $v$ and $w$ are eigenvectors of $M$ with the same eigenvalue, then so is $q = av + bw$, so eigenvectors with the same eigenvalue need not be orthogonal. (3) $M$ has a full orthonormal basis of eigenvectors $v_1, \ldots, v_n$. All eigenvalues and eigenvectors are real. (4) $M$ is diagonalizable: $M = V \Lambda V^\top$ where $V$ is orthogonal ($VV^\top = I_n$), with columns equal to $v_1, \ldots, v_n$, and $\Lambda$ is diagonal, with the corresponding eigenvalues of $M$ as its diagonal entries. So $M = \sum_{i=1}^{n} \lambda_i v_i v_i^\top$.

## Depends on

- [Definition 1 (Lecture 1, Section 2)](001-definition-1.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 1, Section 2](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
