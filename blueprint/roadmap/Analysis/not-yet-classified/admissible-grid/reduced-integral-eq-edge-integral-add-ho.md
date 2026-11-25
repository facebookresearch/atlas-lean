# Reduced Integral eq edge Integral Add Hom

The reduced integral is the additive edge-chain integral evaluated at the filling boundary
chain.

```lean
theorem reducedIntegral_eq_edgeIntegralAddHom {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.reducedIntegral f = D.edgeIntegralAddHom f D.boundaryChain
```
