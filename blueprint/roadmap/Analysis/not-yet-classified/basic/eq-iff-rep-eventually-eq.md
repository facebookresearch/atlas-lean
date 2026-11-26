# Eq iff rep eventually Eq

Two holomorphic germs are equal exactly when their chosen representatives agree near the
spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.eq_iff_rep_eventuallyEq (a : A)
    (f g : HolomorphicNearSpectrum a) :
    f = g ↔ f.rep a =ᶠ[𝓝ˢ (spectrum ℂ a)] g.rep a
```
