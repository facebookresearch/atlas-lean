# L1 contraction with independent anchors

For positive viscosity and bounded continuous initial velocities with integrable difference, the evolved difference remains integrable and its L1 norm cannot increase at any nonnegative time, even when the two fields use independent normalization anchors.

## Exact statement

```lean
theorem burgersSolution_l1_contraction_of_anchors {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν t : ℝ} (hν : 0 < ν) (hi : Integrable (fun x => u x - v x))
    (a b : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution ν u a t x - burgersSolution ν v b t x) ∧
      (∫ x, |burgersSolution ν u a t x - burgersSolution ν v b t x|) ≤ ∫ x, |u x - v x|
```

## Proof

Apply L1 contraction after identifying the anchors by anchor independence.
