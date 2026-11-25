# Rep of Scalars germ

The chosen representative of a scalar-series germ agrees, as a germ,
with the sum of the corresponding formal multilinear series.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_ofScalars_germ
    (a : A) (c : ℕ → ℂ)
    (h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    ((HolomorphicNearSpectrum.ofScalars a c h).rep a : SpectrumGerm a) =
      ((FormalMultilinearSeries.ofScalars ℂ c).sum : SpectrumGerm a)
```
