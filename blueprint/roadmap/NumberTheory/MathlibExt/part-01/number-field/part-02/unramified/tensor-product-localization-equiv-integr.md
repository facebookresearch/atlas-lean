---
article_id: af_a5223b2e535fb6209bc7b34a
declaration: def
origin: cited
statement: formalized
lean: NumberField.IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure
---

# Tensor Product Localization Equiv Integral Closure

Global normalization base-change bridge above an unramified prime: for number
fields `E` and `F` and `p` unramified in `𝓞 F`, tensoring the semilocal
integral-closure identification of `E` with the semilocal ring of `F` identifies
`S_F ⊗[R] S_E` with the integral closure of `S_F` in the base-changed fraction
ring.

This is the normalization-under-étale-base-change route toward the compositum
step `baseChange_ramificationIdx_eq_one` and `isUnramifiedAtPrime_sup` in the
primary Lean source for ATLAS N390. The local-factor/compositum identification
needed to recover those source theorems is not claimed here.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Etale localization](etale-localization.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.Unramified](../../../../../../../sources/v2/MathlibExt.md)
