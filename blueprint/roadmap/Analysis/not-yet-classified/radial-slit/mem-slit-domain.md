# Mem slit Domain

The slit-domain points have norm below one and do not lie on the slit.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem mem_slitDomain {z : ℂ} :
    z ∈ E.slitDomain ↔ ‖z‖ < 1 ∧ z ∉ E.slitSet
```
