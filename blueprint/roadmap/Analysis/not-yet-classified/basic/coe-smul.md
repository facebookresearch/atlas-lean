# Coe smul

The underlying spectrum germ of a scalar multiple is the scalar multiple of the underlying germ.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.coe_smul (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    ((c • f : HolomorphicNearSpectrum a) : SpectrumGerm a) = c • f.1
```
