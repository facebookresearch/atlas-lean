---
article_id: af_006602114fc9b1d56962b483
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.KernelsLemmaWanted.kernels_lemma_pairwise_isCoprime
---

# Kernels lemma pairwise is Coprime

Kernels lemma, finite-family version (primary decomposition machinery): for pairwise coprime
polynomials, the individual kernels are independent and their supremum is the kernel of the
product. The decomposition is internal to the product kernel; it need not span all of `M`.

Proof: induction on the number of polynomials from the two-polynomial case, as in the cited French
Wikipedia article. Mathlib's `Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime` is the
two-polynomial step, and independence follows from `Polynomial.disjoint_ker_aeval_of_isCoprime`
applied to each polynomial and the product of the others.

## Depends on

This node has no prerequisites.

## Proof depends on

- [I Sup Indep ker aeval and i Sup eq of pairwise is Coprime](i-sup-indep-ker-aeval-and-i-sup-eq-of-pa.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.KernelsLemma](../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / kernels lemma; https://fr.wikipedia.org/wiki/Lemme_des_noyaux; S. Axler, Linear Algebra Done Right, 4th ed., Springer (2024), Section 8C.
