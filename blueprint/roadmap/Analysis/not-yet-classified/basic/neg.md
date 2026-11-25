# Neg

The additive inverse of a holomorphic spectrum germ is holomorphic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.neg (a : A) {f : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f) :
    IsHolomorphicNearSpectrum a (-f)
```
