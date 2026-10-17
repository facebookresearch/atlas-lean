---
article_id: af_4f2bc1c52c35a99e2c69699d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: laplaceConvergent_of_isBigO_exp
---

# Laplace Convergent of is Big O exp

Laplace convergence from a source-shaped eventual exponential Big-O bound.

This is the first half of a corrected, strengthened-premise formalization of the
ATLAS N320 intended convergence claim: a locally integrable function with
`f =O[atTop] exp (a * t)` has a convergent Laplace transform for `a < s.re`.
The `LocallyIntegrableOn f (Set.Ici 0)` premise explicitly repairs the missing
endpoint condition: ATLAS's piecewise continuity on `ℝ_{>0}` does not supply
near-zero integrability (counterexample `f(t) = 1/t`); the tail is handled by the
asymptotic integrability API. This is not a literal proof of the under-specified
source wording.

## Depends on

- [Laplace Convergent](../basic/laplace-convergent.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.LaplaceTransform.ExponentialBound](../../../../../../sources/v2/MathlibExt.md)
