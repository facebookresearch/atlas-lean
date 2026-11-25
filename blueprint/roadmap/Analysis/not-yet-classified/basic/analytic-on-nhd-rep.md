# Analytic On Nhd rep

The chosen representative is analytic on a neighborhood of every spectral point.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.analyticOnNhd_rep (a : A)
    (f : HolomorphicNearSpectrum a) :
    AnalyticOnNhd ℂ (f.rep a) (spectrum ℂ a)
```
