# Reduced Integral congr

Integrands agreeing on the reduced trace have equal complete Banach-valued reduced integrals.

```lean
theorem reducedIntegral_congr {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling)
    {f g : ℂ → E} (hfg : Set.EqOn f g D.reducedTrace) :
    D.reducedIntegral f = D.reducedIntegral g
```
