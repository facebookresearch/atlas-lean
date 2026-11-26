# Continuous At reduced Integral cauchy Kernel of not mem reduced Trace

The reduced Cauchy-kernel integral is continuous in its pole off the reduced trace.

```lean
theorem continuousAt_reducedIntegral_cauchyKernel_of_not_mem_reducedTrace
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.reducedTrace) :
    ContinuousAt (fun w : ℂ ↦ D.reducedIntegral (fun ξ ↦ (ξ - w)⁻¹)) z
```
