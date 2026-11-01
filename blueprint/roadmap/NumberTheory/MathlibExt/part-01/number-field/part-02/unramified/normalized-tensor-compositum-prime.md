---
article_id: af_c6ecd5c2bd0deea7a8a623d5
declaration: def
origin: cited
statement: formalized
lean: NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime
---

# Normalized Tensor Compositum Prime

Contracted maximal prime: the correct prime of the normalized tensor algebra
at which to localize to obtain the local factor `Localization.AtPrime Q`.

Let `g := normalizedTensorToCompositumAtPrime E F p h Q` and
`T := Localization.AtPrime Q`. This is the comap of the maximal ideal of the
local ring `T` under `g`. It contains the prime kernel of `g` (see
`normalizedTensorToCompositumAtPrime_ker_le`), but it is in general strictly
larger: for a nonzero prime below `Q`, a nonzero uniformizer lies outside
`RingHom.ker g` yet maps to a nonunit of `T`.

This is a named alternative-normalization prerequisite stage for the missing
`cyclotomic_ramIdx_eq_of_unramified` and
[`baseChange_ramificationIdx_eq_one`, lines 1549--1586](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L1549-L1586)
in the primary Lean source for ATLAS `NumberTheoryI` target N390,
Proposition 19.14. It does not prove
compositum unramifiedness, any `IsLocalization` identification, or the final
maximality theorem.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Normalized Tensor To Compositum At Prime](normalized-tensor-to-compositum-at-prime.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.Unramified](../../../../../../../sources/v2/MathlibExt.md)
