# Of Function add

Taking an analytic representative to its spectrum germ preserves addition.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.ofFunction_add (a : A)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a))
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a (f + g) (hf.add hg) =
      HolomorphicNearSpectrum.ofFunction a f hf +
        HolomorphicNearSpectrum.ofFunction a g hg
```
