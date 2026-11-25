# To Cycle integral eq zero of differentiable On region

A scalar function differentiable on the entire filled grid region has
zero integral around the associated rectilinear cycle.

```lean
theorem toCycle_integral_eq_zero_of_differentiableOn_region
    (D : GridFilling) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D.region) :
    D.toCycle.integral f = 0
```
