# The rank of a Kronecker product is the product of the ranks

Over a field, every matrix $A$ contains a nonsingular $\operatorname{rank}A\times\operatorname{rank}A$ submatrix, and $\operatorname{rank}(A\otimes B)=\operatorname{rank}A\cdot\operatorname{rank}B$. Consequently the $k$-fold Kronecker power satisfies $\operatorname{rank}A^{\otimes k}=(\operatorname{rank}A)^k$.

## Proof sketch

The upper bound follows from factorizations $A=UV$, $B=U'V'$ with inner dimensions equal to the ranks. For the lower bound, the Kronecker product of nonsingular $r\times r$ and $r'\times r'$ submatrices is a submatrix of $A\otimes B$ with determinant $\det(A_0)^{r'}\det(B_0)^{r}\neq0$.

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
