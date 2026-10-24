---
article_id: af_c442a882763518d410a63b9e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond
---

# Partition Polynomial iterated Deriv eq sum stirling Second

The derivative formula for the partition polynomial, expressed using Stirling numbers of the
second kind.

The partition `λ = ⟨1^m₁, …, k^mₖ⟩` in frequency notation has largest part `k`
(`m k ≠ 0`, support in `Icc 1 k`) and partition polynomial `f(y) = ∑ mᵢ yⁱ`; the
`d`th derivative at nonzero `x` is the displayed Stirling recursion, valid for
`0 ≤ d ≤ k` (the second sum is empty for `d = 0`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Partition Polynomial iterated Deriv eq sum stirling Second general](partition-polynomial-iterated-deriv-eq-s.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.PartitionPolynomialDerivatives](../../../../../../../../sources/v2/MathlibExt.md)
- Madeline Locus Dawsey, Tyler Russell, and Dannie Urban, "Derivatives and Integrals of Polynomials Associated with Integer Partitions," Journal of Integer Sequences 25 (2022), Article 22.5.1, Theorem 1 (label `derivativethm`), lines 108–114, <https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.tex>.
