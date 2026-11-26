# Odd cycles cancel in the determinant of a skew-symmetric matrix

Let $A$ be a square matrix over a commutative ring with $A^{T}=-A$ and zero diagonal (the latter is automatic when $2$ is not a zero divisor). In the Leibniz expansion $\det A=\sum_\sigma\operatorname{sgn}(\sigma)\prod_iA_{\sigma(i),i}$, the terms of permutations having a cycle of odd length cancel in pairs, so $\det A$ equals the sum over permutations all of whose cycles have even length. In particular every odd-dimensional such matrix has determinant zero. The zero diagonal is needed: over $\mathbb{F}_2$ the $1\times1$ matrix $(1)$ satisfies $A^T=-A$ and has determinant $1$.

## Proof sketch

Permutations with a fixed point contribute $0$ because the diagonal vanishes. Otherwise reverse the odd cycle (of length at least $3$) through the least point that lies on an odd cycle: this is a sign-preserving involution on such permutations that negates the product, because each of the odd number of entries on the reversed cycle is replaced by its negative.

## Depends on

- [Leibniz formula for the determinant](../determinants-of-matrices/leibniz-formula/det-apply.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
