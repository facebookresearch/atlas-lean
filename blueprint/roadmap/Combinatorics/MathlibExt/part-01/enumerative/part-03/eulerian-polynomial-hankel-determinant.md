---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.eulerianPolynomial_hankelDeterminant
---

# Eulerian Polynomial Hankel

The Hankel determinant of order `n + 1` for the Eulerian polynomials is
`X ^ choose (n + 1) 2` times the product of the squared factorials from `1` to `n`.

Proof: Barry's Eulerian moment recurrence gives the zeroth column of a weighted-Motzkin table
with down-step weights `λ_k = k² X`. The weighted-Motzkin determinant theorem and a product
simplification then give the stated formula.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Hankel Transform](../../../../../NumberTheory/MathlibExt/part-06/hankel-transform/hankel-transform.md)
- [Heilermann Weighted Motzkin Determinant](../part-04/hankel-transform-eq-prod-of-weighted-mot.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.EulerianPolynomialHankel](../../../../../../sources/v2/MathlibExt.md)
- Paul Barry, "Eulerian Polynomials as Moments, via Exponential Riordan Arrays," Journal of Integer Sequences 14 (2011), Article 11.9.5, corollary lines 240–243, <https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry7/barry172.tex>. Eulerian closed form `W_{n,k}` at lines 93–94.
