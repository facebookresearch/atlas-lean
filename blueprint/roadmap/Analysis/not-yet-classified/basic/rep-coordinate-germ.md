# Rep coordinate germ

The representative of the coordinate germ has the same germ as the identity scalar function.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_coordinate_germ (a : A) :
    ((HolomorphicNearSpectrum.coordinate a).rep a : SpectrumGerm a) =
      ((id : ℂ → ℂ) : SpectrumGerm a)
```
