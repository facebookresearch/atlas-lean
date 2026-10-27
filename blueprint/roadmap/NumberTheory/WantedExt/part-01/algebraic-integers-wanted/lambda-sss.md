---
article_id: af_1f1498933bcca4b60ce436bd
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.AlgebraicIntegersWanted.AlgebraicIntegers.lambda_SSS
---

# Lambda SSS

Take `λ_SSS` to be the greatest real number `λ` such that, for any `ε > 0`,
there are only finitely many totally positive algebraic integers α satisfying
`tr(α) < (λ − ε) * deg(α)`. Note that the paper said "least real number",
but this is clearly a typo, as this set does not have a lower bound. Defining
it as the greatest real number is consistent with how this constant is defined in
another paper by the same author, namely in Orloski, Sardari and Smith: "New
lower bounds for the Schur-Siegel-Smyth trace problem" (arXiv:2401.03252).
There, `λ_SSS` is defined as the limit inferior of `tr(α)/deg(α)` over all
totally positive `α`, which is exactly the *greatest* real number `λ` such that
for all `ε > 0`, only finitely many `α` have `tr(α)/deg(α) < λ - ε`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Totally Positive](is-totally-positive.md)
- [Degree](degree.md)
- [Trace](trace.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.AlgebraicIntegersWanted](../../../../../sources/v2/WantedExt.md)
