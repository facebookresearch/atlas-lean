# Rep germ

The chosen representative has exactly the original spectrum germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_germ (a : A)
    (f : HolomorphicNearSpectrum a) :
    (f.rep a : SpectrumGerm a) = f.1
```
