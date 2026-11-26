# Odd cycles cancel in the determinant of a skew-symmetric matrix

Let $A$ be a square matrix over a commutative ring with $A^{T}=-A$. In the Leibniz expansion $\det A=\sum_\sigma\operatorname{sgn}(\sigma)\prod_iA_{\sigma(i),i}$, the terms of permutations having a cycle of odd length cancel in pairs, so $\det A$ equals the sum over permutations all of whose cycles have even length. In particular an odd-dimensional skew-symmetric matrix over a ring in which $2$ is not a zero divisor (or any ring, by this cancellation) has determinant zero.

## Proof sketch

Reverse the odd cycle through the least point that lies on an odd cycle: this is a sign-preserving involution on such permutations that negates the product, because each of the odd number of entries on the reversed cycle is replaced by its negative.

## Depends on

- [Leibniz formula for the determinant](../determinants-of-matrices/leibniz-formula/det-apply.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
