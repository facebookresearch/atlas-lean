# Spectrum subset analytic Domain

The representative analytic domain contains the complex spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.spectrum_subset_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) :
    spectrum ℂ a ⊆ f.analyticDomain a
```
