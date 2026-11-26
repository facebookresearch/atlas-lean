# Exists continuous extension on comparison Carrier

A scalar function continuous on a containing set extends globally and agrees on the closed
comparison carrier.

```lean
theorem exists_continuous_extension_on_comparisonCarrier
    {D E : GridFilling} {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (hsub : D.comparisonCarrier E ⊆ U) :
    ∃ g : ℂ → ℂ, Continuous g ∧ Set.EqOn g f (D.comparisonCarrier E)
```
