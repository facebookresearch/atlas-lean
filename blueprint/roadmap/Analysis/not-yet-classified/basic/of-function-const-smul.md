# Of Function const smul

Taking an analytic representative to its spectrum germ preserves complex scalar multiplication.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.ofFunction_const_smul (a : A) (c : ℂ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a (c • f) hf.const_smul =
      c • HolomorphicNearSpectrum.ofFunction a f hf
```
