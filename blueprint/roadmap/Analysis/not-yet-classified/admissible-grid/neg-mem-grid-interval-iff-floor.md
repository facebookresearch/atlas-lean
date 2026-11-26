# Neg mem grid Interval iff floor

For positive `t`, membership of `-x` in `(-(n+1)/t,-n/t]` is equivalent to `floor(t*x)=n`.

```lean
theorem neg_mem_gridInterval_iff_floor {t : ℝ} (ht : 0 < t)
    (n : ℤ) (x : ℝ) :
    -x ∈ Ioc (-(((n : ℝ) + 1) / t)) (-((n : ℝ) / t)) ↔
      ⌊t * x⌋ = n
```
