# Integral contraction for ordered Burgers data

Let u and v be bounded continuous initial velocities with u ≤ v and integrable difference v−u. For positive viscosity and every nonnegative time, the evolved difference is integrable and its integral is at most the initial difference integral. A common arbitrary anchor is used. Integrability of either velocity separately is not required.

## Exact statement

```lean
theorem burgersSolution_ordered_integral_le {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν t : ℝ} (hν : 0 < ν) (h : ∀ x, u x ≤ v x)
    (hi : Integrable (fun x => v x - u x)) (a : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution ν v a t x - burgersSolution ν u a t x) ∧
      (∫ x, burgersSolution ν v a t x - burgersSolution ν u a t x) ≤ ∫ x, v x - u x
```

## Proof

Use order preservation, bound the logarithmic primitive, integrate on finite intervals, and exhaust the real line.
