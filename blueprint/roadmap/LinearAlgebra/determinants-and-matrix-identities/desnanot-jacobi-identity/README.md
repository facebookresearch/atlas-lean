# Desnanot–Jacobi identity

Let $R$ be a commutative ring and let $C$ be an $(n + 2) \times (n + 2)$ matrix over $R$. Write $C^a_b$ for $C$ with row $a$ and column $b$ deleted, and, for distinct indices $i$ and $j$, $C^{ij}_{ij}$ for $C$ with rows and columns $i$ and $j$ deleted (an empty matrix with determinant $1$ when $n = 0$). Then

$$\det C \cdot \det C^{ij}_{ij} = \det C^i_i \det C^j_j - \det C^i_j \det C^j_i.$$

## Idea

The identity relates the determinant of a matrix to four of its minors of one size smaller and one minor of two sizes smaller. Applied with the first and last rows and columns, it gives Dodgson's condensation method: when the interior minor $\det C^{ij}_{ij}$ is invertible, the determinant of an $(n+2) \times (n+2)$ matrix is computed from the determinants of its contiguous $(n+1) \times (n+1)$ and $n \times n$ blocks, like a $2 \times 2$ determinant of determinants divided by that minor; the method breaks down when an interior minor vanishes. The identity is a special case of Sylvester's determinant identity and follows from Jacobi's theorem on minors of the adjugate. It also underlies the alternating sign matrices of Robbins and Rumsey.

## Statements

- [Carroll (Desnanot–Jacobi) identity](carroll-identity.md)
