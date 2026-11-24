# Products of symmetric unimodal polynomials

Let $P(x) = \sum_{i=0}^{m} a_i x^i$ and $Q(x) = \sum_{i=0}^{n} b_i x^i$ be real polynomials
with nonnegative coefficients. Suppose $(a_0, \dots, a_m)$ and $(b_0, \dots, b_n)$ are symmetric
($a_i = a_{m-i}$, $b_i = b_{n-i}$) and unimodal. Then the coefficients $(c_0, \dots, c_{m+n})$ of
$P(x)Q(x)$ are nonnegative, symmetric and unimodal. Here $m$ and $n$ are upper bounds, not
necessarily the degrees: the coefficient lists may be padded by zeros, and either polynomial
may be zero.

To see why, decompose each coefficient list into concentric interval indicators, weighted by the
successive increases on its left half (starting from zero). A coefficient in the product of two
interval indicators counts pairs of indices with that sum. The count increases toward the center,
possibly levels off, and then decreases symmetrically. All these products have the same center
$(m+n)/2$, so their nonnegative weighted sum has the same properties.

Without symmetry the product of unimodal polynomials need not be unimodal:
$(1 + x + 4x^2)^2 = 1 + 2x + 9x^2 + 8x^3 + 16x^4$.

## Sources

- Richard P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Chapter 1, Exercise 50(c).
