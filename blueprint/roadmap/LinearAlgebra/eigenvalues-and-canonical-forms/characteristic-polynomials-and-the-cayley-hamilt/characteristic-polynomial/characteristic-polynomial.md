# Characteristic polynomial of an operator

Let $V$ be a nonzero finite-dimensional vector space over $\mathbb F$, where $\mathbb F$ is $\mathbb R$ or $\mathbb C$,
and let $T \colon V \to V$ be a linear map. The characteristic polynomial of $T$ is the function
$z \mapsto \det(zI - T)$ on $\mathbb F$, where $I$ is the identity map of $V$ and $\det$ is the determinant of a linear
map from $V$ to itself. It is a monic polynomial of degree $\dim V$.

## Proof

Let $b_1, \dots, b_n$ be a basis of $V$, where $n = \dim V$, and let $A$ be the matrix of $T$ in it. As
$(zI - T) b_k = z b_k - T b_k$, the matrix of $zI - T$ in this basis has entries $z\delta_{jk} - A_{jk}$, where
$\delta_{jk}$ is $1$ if $j = k$ and $0$ otherwise. The determinant of a linear map is the determinant of its matrix in
any basis indexed by a finite set, so $\det(zI - T)$ is the determinant of this $n \times n$ matrix. By the Leibniz
formula this determinant is a sum, over the permutations of $\{1, \dots, n\}$, of signed products of entries, so it is a
polynomial in $z$. The identity permutation contributes $(z - A_{11}) \cdots (z - A_{nn})$. Every other permutation
moves at least two indices, since a permutation fixing all indices but one fixes that one too; so its product has at
most $n - 2$ diagonal entries, the only entries that involve $z$. Hence the polynomial is monic of degree $n$.

## Depends on

- [Determinant of a linear map](../../../determinants-and-matrix-identities/determinants-of-linear-maps/determinant-of-a-linear-map/det.md)
- [Finite-dimensional vector space](../../../bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)
- [Dimension of a finite-dimensional vector space](../../../bases-and-dimension/bases-and-coordinates/dimension/finite-dimension.md)

## Proof depends on

- [Basis of a vector space](../../../bases-and-dimension/bases-and-coordinates/bases/vector-space-basis.md)
- [The determinant of a linear map is the determinant of its matrix in any basis](../../../determinants-and-matrix-identities/determinants-of-linear-maps/determinant-of-a-linear-map/det-to-matrix.md)
- [Leibniz formula for the determinant](../../../determinants-and-matrix-identities/determinants-of-matrices/leibniz-formula/det-apply.md)

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 9.63, with 9.41, 9.46 and 9.53 (version read: the open-access PDF dated 4 November 2026).
