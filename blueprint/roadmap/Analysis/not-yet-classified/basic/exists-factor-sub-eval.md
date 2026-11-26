# Exists factor sub eval

An element of `Hol(a)` admits the linear factorization used in the classical
proof of the spectral mapping theorem at every spectral point.  The divided
difference is analytic even when the zero has higher multiplicity.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.exists_factor_sub_eval
    (a : A) (f : HolomorphicNearSpectrum a) {z₀ : ℂ}
    (hz₀ : z₀ ∈ spectrum ℂ a) :
    ∃ g : HolomorphicNearSpectrum a,
      f - algebraMap ℂ (HolomorphicNearSpectrum a) (f.rep a z₀) =
        (HolomorphicNearSpectrum.coordinate a -
          algebraMap ℂ (HolomorphicNearSpectrum a) z₀) * g
```
