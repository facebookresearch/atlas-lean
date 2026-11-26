# The Cauchy–Binet formula

Let $R$ be a commutative ring, $A$ an $n\times k$ matrix and $B$ a $k\times n$ matrix over $R$. Then

$$
\det(AB)=\sum_{S}\det(A_{[n],S})\,\det(B_{S,[n]}),
$$

the sum over all $n$-element subsets $S\subseteq\{1,\dots,k\}$ (and $\det(AB)=0$ if $k<n$).

## Proof sketch

Expand $\det(AB)$ multilinearly in the columns of $AB$, each a combination of columns of $A$; terms with a repeated column vanish, and grouping the remaining terms by the set of columns used gives the product of the two minors by antisymmetry.

## Depends on

- [Leibniz formula for the determinant](../determinants-of-matrices/leibniz-formula/det-apply.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- F. R. Gantmacher, "The Theory of Matrices", Vol. 1, Chelsea, 1959.
