---
article_id: af_a1267dbdb5ff1ad54bd0dc8a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.polynomially_recursive_MC_finite
---

# Polynomially recursive MC finite

Polynomially recursive integer sequences are MC-finite, including the holonomic
special case: a sequence that is PRS over `ℤ` and `n` is MC-finite, and in
particular a sequence that is holonomic over `ℤ` is MC-finite.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is MCFinite](is-mcfinite-2.md)
- [Is MCFinite of mv Polynomial recursion](is-mcfinite-of-mv-polynomial-recursion.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite](../../../../../../sources/v2/MathlibExt.md)
- Yuval Filmus, Eldar Fischer, and Johann A. Makowsky, with Vsevolod Rakita, "MC-Finiteness of Restricted Set Partition Functions," Journal of Integer Sequences 26 (2023), Article 23.7.4, Theorem (label th:MC), lines 422–427, with the MC-finite definition at lines 281–286 and the holonomic/PRS definitions at lines 387–412, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>. It follows from `isMCFinite_of_mvPolynomial_recursion` and `IsPRecursiveSequence.isMCFinite`; in the holonomic premise the conditions `0 < k`, `P 1 ≠ 0` and `P k ≠ 0` are unused and keep the source's shape. Proves `Wanted` entry `polynomially_recursive_MC_finite`.
