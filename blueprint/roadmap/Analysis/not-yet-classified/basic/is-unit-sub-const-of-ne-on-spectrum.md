# Is Unit sub const of ne on spectrum

If a holomorphic spectrum germ avoids a scalar value on the spectrum,
then subtracting that scalar gives a unit of `Hol(a)`.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.isUnit_sub_const_of_ne_on_spectrum
    (a : A) (f : HolomorphicNearSpectrum a) {c : ℂ}
    (hc : ∀ z ∈ spectrum ℂ a, f.rep a z ≠ c) :
    IsUnit (f - algebraMap ℂ (HolomorphicNearSpectrum a) c)
```
