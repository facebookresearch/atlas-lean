# Finite free additive convolution of polynomials

For monic polynomials $p(x) = \sum_{i=0}^{d} (-1)^{i} a_i x^{d-i}$ and $q(x) = \sum_{i=0}^{d} (-1)^{i} b_i x^{d-i}$ of degree $d$, their *finite free additive convolution* is

$$
(p \boxplus_d q)(x) = \sum_{k=0}^{d} (-1)^{k} x^{d-k} \sum_{i + j = k} \frac{(d-i)!\,(d-j)!}{d!\,(d-k)!}\, a_i b_j .
$$

If $p = \det(xI - A)$ and $q = \det(xI - B)$ for $d \times d$ Hermitian $A, B$, then $p \boxplus_d q = \mathbb{E}_Q\det(xI - A - QBQ^{*})$ over Haar-random unitary (or uniformly random signed permutation) $Q$.

## Depends on

- [Real-rooted polynomials](../../../Algebra/zeros-of-polynomials/real-rooted-polynomials/is-real-rooted.md)

## Sources

- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Finite free convolutions of polynomials", Probability Theory and Related Fields 182 (2022); arXiv:1504.00350.
