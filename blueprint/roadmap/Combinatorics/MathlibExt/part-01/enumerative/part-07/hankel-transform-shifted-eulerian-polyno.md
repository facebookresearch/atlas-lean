---
article_id: af_3bf228ab33c82d5c32ee75ad
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hankel_transform_shifted_eulerian_polynomials
---

# Shifted Eulerian Hankel

Hankel transform of the shifted Eulerian polynomials `P_{n+1}(x)`.
The determinant of `(P_{i+j+1}(x))` over `Fin (n + 1)` equals
`(2 * x) ^ Nat.choose (n + 1) 2` times the product over `Finset.range n`
of `Nat.choose (k + 3) 2 ^ (n - (k + 1))`, where `P` is built from
the closed-form coefficients `W`.

Proof: The closed Eulerian coefficients identify a weighted-Motzkin Stieltjes table with
Jacobi weights `euAlpha` and `euBeta`; its determinant follows by the Heilermann-Flajolet LDU
route used by Barry and discussed by Krattenthaler.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Hankel Transform](../../../../../NumberTheory/MathlibExt/part-06/hankel-transform/hankel-transform.md)
- [Heilermann Weighted Motzkin Determinant](../part-04/hankel-transform-eq-prod-of-weighted-mot.md)
- [Stirling Second mul factorial eq sum](../part-08/stirling-second-explicit/stirling-second-mul-factorial-eq-sum.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.ShiftedEulerianHankel](../../../../../../sources/v2/MathlibExt.md)
- Paul Barry, "Eulerian Polynomials as Moments, via Exponential Riordan Arrays," Journal of Integer Sequences 14 (2011), Article 11.9.5, corollary lines 312–315, <https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry7/barry172.tex>. Eulerian closed form `W_{n,k}` at lines 93–94.
