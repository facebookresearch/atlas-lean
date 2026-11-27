# Angular Sublevel Length le

Every strict angular sublevel set has length at most `2π`.

```lean
theorem angularSublevelLength_le (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelLength u r K ≤ ENNReal.ofReal (2 * Real.pi)
```
