---
article_id: af_e1c7edc819e17343620668fe
declaration: def
origin: cited
statement: formalized
lean: NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime
---

# Normalized Tensor Localization To Compositum At Prime

Canonical localization map: the universal property of
`Localization.AtPrime` applied at the contracted maximal prime. An element
outside the contracted prime maps outside the maximal ideal of the local target
`T`, hence to a unit.

This is a plain `RingHom`, not an `AlgHom`: no `Algebra A S` or
`IsScalarTower A C S` data is installed, since that instance search is fragile.
No `IsLocalization` or `AlgEquiv` claim is made here: the missing
bijection/local-factor identification remains a later infrastructure problem,
and localization at `RingHom.ker g` is in general false.

## Depends on

- [Normalized Tensor Compositum Prime](normalized-tensor-compositum-prime.md)
- [Normalized Tensor Compositum Prime is Prime](normalized-tensor-compositum-prime-is-pr.md)

## Proof depends on

- [Normalized Tensor To Compositum At Prime](normalized-tensor-to-compositum-at-prime.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.Unramified](../../../../../../../sources/v2/MathlibExt.md)
