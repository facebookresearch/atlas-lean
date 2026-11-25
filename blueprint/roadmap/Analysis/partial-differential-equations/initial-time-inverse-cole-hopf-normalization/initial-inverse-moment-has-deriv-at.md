# Averaged Burgers flux on an open time domain

Let I be any open real time set. For a field jointly C² on I × ℝ, at a time t in I where Burgers holds at every spatial point, the weighted unit-interval velocity moment has the derivative displayed below. The spatial anchor is arbitrary. This identity imposes no sign or nonzero condition on the viscosity and no boundedness condition on the field.

## Exact statement

```lean
theorem initialInverseMoment_hasDerivAt {u : ℝ → ℝ → ℝ} {ν t : ℝ}
    {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ univ)) (ht : t ∈ I)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (a : ℝ) :
    HasDerivAt (initialInverseMoment u a)
      (ν * (u t (a + 1) - u t a) - (∫ y in a..a + 1, u t y ^ 2) / 2 -
        (ν * deriv (u t) a - u t a ^ 2 / 2)) t
```

## Proof

Integrate the Burgers flux identity by parts over the unit interval and differentiate the weighted velocity integral.
