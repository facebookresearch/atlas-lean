# Is Holomorphic Near Spectrum coe

A global scalar function determines a holomorphic spectrum germ exactly when it is analytic on
a neighborhood of every spectral point.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem isHolomorphicNearSpectrum_coe (a : A) (f : ℂ → ℂ) :
    IsHolomorphicNearSpectrum a (f : SpectrumGerm a) ↔
      AnalyticOnNhd ℂ f (spectrum ℂ a)
```
