# L1 contraction of Burgers velocity differences

For positive viscosity, bounded continuous initial velocities whose difference is integrable have an integrable evolved difference at every nonnegative time. Its L1 norm is no larger than the initial L1 norm. A common arbitrary normalization anchor is used; neither initial velocity needs to be integrable individually.

## Exact statement

```lean
theorem burgersSolution_l1_contraction {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν t : ℝ} (hν : 0 < ν) (hi : Integrable (fun x => u x - v x))
    (a : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution ν u a t x - burgersSolution ν v a t x) ∧
      (∫ x, |burgersSolution ν u a t x - burgersSolution ν v a t x|) ≤ ∫ x, |u x - v x|
```

## Proof

Enclose the two data by their pointwise minimum and maximum and apply ordered integral contraction.
