# Mem slit Set

A complex point lies on the slit exactly when its imaginary part is zero and its real part
belongs to the radius union.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem mem_slitSet {z : ℂ} :
    z ∈ E.slitSet ↔ z.re ∈ E.radiusSet ∧ z.im = 0
```
