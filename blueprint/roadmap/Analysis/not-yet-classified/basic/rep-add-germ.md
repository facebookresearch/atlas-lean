# Rep add germ

The representative of a sum has the sum of the two representative germs.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.rep_add_germ (a : A)
    (f g : HolomorphicNearSpectrum a) :
    ((f + g).rep a : SpectrumGerm a) =
      (f.rep a : SpectrumGerm a) + (g.rep a : SpectrumGerm a)
```
