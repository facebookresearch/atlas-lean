# Rep const germ

The representative of a constant germ has the same germ as the corresponding constant function.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_const_germ (a : A) (c : ℂ) :
    ((HolomorphicNearSpectrum.const a c).rep a : SpectrumGerm a) =
      ((fun _ : ℂ ↦ c) : SpectrumGerm a)
```
