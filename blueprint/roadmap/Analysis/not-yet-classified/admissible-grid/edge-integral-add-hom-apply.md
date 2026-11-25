# Edge Integral Add Hom apply

The additive edge-chain integral is the finite sum weighted by its integer edge coefficients.

```lean
theorem edgeIntegralAddHom_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E)
    (c : GridEdge →₀ ℤ) :
    D.edgeIntegralAddHom f c = c.sum fun e n ↦ n • D.edgeIntegral e f
```
