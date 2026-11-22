# First-order expansion of the determinant

Let $R$ be a commutative ring and let $A$ and $B$ be square matrices over $R$ indexed by a finite set $n$. The first-order term of the determinant at $B$ in the direction $A$ is $L_B(A) = \sum_{i \in n} \det B^{(i)}$, where $B^{(i)}$ is the matrix $B$ with its $i$-th row replaced by the $i$-th row of $A$.

## Idea

The determinant is a polynomial in the entries, so $\det(B + tA)$ is a polynomial in $t$; its constant term is $\det B$ and its linear coefficient is $L_B(A)$. Because the determinant is linear in each row, that coefficient is obtained by replacing one row of $B$ at a time by the corresponding row of $A$. The map $A \mapsto L_B(A)$ is linear, and when $B$ is invertible it equals $\det(B)\operatorname{tr}(B^{-1}A)$, the derivative of the determinant in the direction $A$. Along a rank-one direction $uv^{\mathsf T}$ there are no higher terms: $\det(B + t\,uv^{\mathsf T})$ is affine in $t$.

## Statements

- [First-order term of the determinant](det-linear.md)
- [Additivity of the first-order term of the determinant](det-linear-add.md): additivity
- [Homogeneity of the first-order term of the determinant](det-linear-smul.md): homogeneity
- [The coefficient of $X$ in $\det(B + XA)$](coeff-one-det-add-x-smul.md): it is the coefficient of $X$ in $\det(B + XA)$
- [The determinant is affine along a rank-one direction](det-add-smul-vec-mul-vec.md): along a rank-one direction the determinant is affine
