# Algebra Map apply

The scalar algebra map into holomorphic spectrum germs is the constant-germ map.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.algebraMap_apply (a : A) (c : ℂ) :
    algebraMap ℂ (HolomorphicNearSpectrum a) c =
      HolomorphicNearSpectrum.const a c
```
