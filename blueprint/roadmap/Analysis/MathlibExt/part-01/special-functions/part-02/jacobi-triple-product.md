---
article_id: af_eaf07707f0d439ca445f55ea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product
---

# Jacobi Triple Product

Jacobi's triple product identity: for `z ≠ 0` and `‖q‖ < 1`, the bilateral
series `∑' n : ℤ, z ^ n * q ^ (n ^ 2)` is summable, the factor family is
multipliable, and the sum equals the product
`∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + z * q ^ (2 * n + 1)) *
  (1 + z⁻¹ * q ^ (2 * n + 1))`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gauss Binom](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-03/gaussian-binomial/gauss-binom.md)
- [Gauss Binom eq zero of lt](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-03/gaussian-binomial/gauss-binom-eq-zero-of-lt.md)
- [Gauss Binom mul q Poch Fin mul q Poch Fin](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-03/gaussian-binomial/gauss-binom-mul-q-poch-fin-mul-q-poch-fi.md)
- [Gauss Binom succ succ](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-03/gaussian-binomial/gauss-binom-succ-succ.md)
- [Gauss Binom zero right](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-03/gaussian-binomial/gauss-binom-zero-right.md)
- [Q Poch Fin](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-03/gaussian-binomial/q-poch-fin.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct](../../../../../../sources/v2/MathlibExt.md)
- Aritram Dhar, Avi Mukhopadhyay, and Rishabh Sarma, "Generalization of the Extended Minimal Excludant of Andrews and Newman," Journal of Integer Sequences 26 (2023), Article 23.3.7, theorem at source lines 455-458 of `https://cs.uwaterloo.ca/journals/JIS/VOL26/Sarma/sarma5.tex`.
