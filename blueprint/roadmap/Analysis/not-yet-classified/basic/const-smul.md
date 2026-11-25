# Const smul

Complex scalar multiplication preserves holomorphic spectrum germs.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.const_smul (a : A) (c : ℂ)
    {f : SpectrumGerm a} (hf : IsHolomorphicNearSpectrum a f) :
    IsHolomorphicNearSpectrum a (c • f)
```
