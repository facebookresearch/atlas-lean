# Of Function eq iff eventually Eq

Two analytic scalar representatives define the same holomorphic germ exactly when they agree on
a neighborhood of the spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.ofFunction_eq_iff_eventuallyEq (a : A)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a))
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a f hf =
        HolomorphicNearSpectrum.ofFunction a g hg ↔
      f =ᶠ[𝓝ˢ (spectrum ℂ a)] g
```
