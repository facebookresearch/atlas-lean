# Rep const smul germ

The representative of a scalar multiple has the scalar multiple of the representative germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_const_smul_germ (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    ((c • f).rep a : SpectrumGerm a) =
      c • (f.rep a : SpectrumGerm a)
```
