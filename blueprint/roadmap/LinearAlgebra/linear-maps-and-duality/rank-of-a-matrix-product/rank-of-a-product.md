# Rank of a product of matrices

Let $K$ be a field, let $A$ be an $m \times r$ matrix and $B$ an $r \times n$ matrix over $K$.
Then $\operatorname{rank}(AB) \le \min(\operatorname{rank} A, \operatorname{rank} B) \le r$. In
particular, a matrix that factors through $K^r$, as $AB$ does, has rank at most $r$.

Proof: every column of $AB$ is a linear combination of the columns of $A$, so the column space of
$AB$ lies in that of $A$ and $\operatorname{rank}(AB) \le \operatorname{rank} A$. Applying this to
$(AB)^{\mathsf{T}} = B^{\mathsf{T}} A^{\mathsf{T}}$ gives
$\operatorname{rank}(AB) \le \operatorname{rank} B^{\mathsf{T}} = \operatorname{rank} B$. Both
ranks are at most $r$, the number of columns of $A$.

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., Exercise 23 in Section 3B ($\dim \operatorname{range} ST \le \min\{\dim \operatorname{range} S, \dim \operatorname{range} T\}$ for linear maps), with 3.43 (the matrix of a product of linear maps is the product of their matrices) and 3.78 (the dimension of the range of a linear map equals the column rank of its matrix). Axler works over $\mathbb{R}$ or $\mathbb{C}$; the argument above holds over any field.
