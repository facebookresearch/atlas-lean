# Mul

The product of two holomorphic spectrum germs is holomorphic.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem IsHolomorphicNearSpectrum.mul (a : A) {f g : SpectrumGerm a}
    (hf : IsHolomorphicNearSpectrum a f)
    (hg : IsHolomorphicNearSpectrum a g) :
    IsHolomorphicNearSpectrum a (f * g)
```
