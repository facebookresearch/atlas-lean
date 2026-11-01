---
article_id: af_5dae7cd83dc70635d5dd8ed0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.andrews_jacobi_triple_product
---

# Andrews jacobi triple product

Andrews' equivalent form of Jacobi's triple product identity: for `‖q‖ < 1`
and `0 < i ≤ k`, the bilateral series
`∑' n : ℤ, (-1) ^ n * q ^ ((2k+1) * n * (n+1) / 2 - i * n)` equals the stated
triple Euler product. The source equation does not restate the `0 < i ≤ k`
hypotheses alongside it; they are needed (at `i = 0` the product side has a
zero factor while the series side does not vanish).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Jacobi Triple Product](../../part-02/jacobi-triple-product.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.AndrewsJacobiTripleProduct](../../../../../../../sources/v2/MathlibExt.md)
- Aritram Dhar, Avi Mukhopadhyay, and Rishabh Sarma, "Generalization of the Extended Minimal Excludant of Andrews and Newman," Journal of Integer Sequences 26 (2023), Article 23.3.7, Theorem (Andrews, An98 p. 22, label JTP1), lines 459–462, https://cs.uwaterloo.ca/journals/JIS/VOL26/Sarma/sarma5.tex
