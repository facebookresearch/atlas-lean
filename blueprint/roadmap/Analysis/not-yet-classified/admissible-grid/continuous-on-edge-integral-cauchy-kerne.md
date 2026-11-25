# Continuous On edge Integral cauchy Kernel

The Cauchy-kernel integral along one grid edge varies continuously with
the pole away from that edge.

```lean
theorem continuousOn_edgeIntegral_cauchyKernel (D : GridFilling) (e : GridEdge) :
    ContinuousOn (fun z : ℂ ↦ D.edgeIntegral e (fun ξ ↦ (ξ - z)⁻¹))
      (D.edgeTrace e)ᶜ
```
