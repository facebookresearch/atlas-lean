---
article_id: af_29d15ea0aeaf886770ede3af
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: differentiableOn_laplace_of_isBigO_exp
---

# Differentiable On laplace of is Big O exp

Holomorphy of the Laplace transform from an eventual exponential Big-O bound.

This completes the source-shaped endpoint as a corrected, strengthened-premise
formalization of the ATLAS N320 intended holomorphy claim: with
`LocallyIntegrableOn f (Set.Ici 0)` explicitly repairing the missing endpoint
condition, an eventual bound `f =O[atTop] exp (a * t)` gives holomorphy on
`{s | a < s.re}`. ATLAS's piecewise continuity on `ℝ_{>0}` does not supply
near-zero integrability (counterexample `f(t) = 1/t`). The `Ici 0` hypothesis is
load-bearing: local integrability on the open ray plus an `atTop` bound would not
suffice. This is not a literal proof of the under-specified source wording.

## Depends on

- [Laplace](../basic/laplace.md)

## Proof depends on

- [Laplace Convergent](../basic/laplace-convergent.md)
- [Laplace Convergent of is Big O exp](laplace-convergent-of-is-big-o-exp.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.LaplaceTransform.ExponentialBound](../../../../../../sources/v2/MathlibExt.md)
