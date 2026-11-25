# Rank of a product of matrices

Let $K$ be a field, $A$ an $m \times r$ matrix and $B$ an $r \times n$ matrix over $K$. Then $\operatorname{rank}(AB) \le \min(\operatorname{rank} A, \operatorname{rank} B) \le r$.

## Idea

Every column of $AB$ is a combination of the columns of $A$, so the column space of $AB$ lies in that of $A$; transposing gives the bound by $\operatorname{rank} B$. In words, a composite of linear maps cannot have a larger image than either factor allows, and a matrix that factors through $K^r$ has rank at most $r$. This is why low-rank approximations are written as products $AB$ with a thin inner dimension, and why the rank of a matrix equals the smallest $r$ for which it factors through $K^r$. Sylvester's rank inequality $\operatorname{rank}(AB) \ge \operatorname{rank} A + \operatorname{rank} B - r$ gives the matching lower bound.

## Statements

- [Rank of a product of matrices](rank-of-a-product.md)
