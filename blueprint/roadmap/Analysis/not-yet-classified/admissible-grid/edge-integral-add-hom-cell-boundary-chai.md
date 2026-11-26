# Edge Integral Add Hom cell Boundary Chain

Integrating a cell's four signed canonical edges gives its counterclockwise rectangle boundary
integral.

```lean
theorem edgeIntegralAddHom_cellBoundaryChain {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) (v : GridIndex) :
    D.edgeIntegralAddHom f (cellBoundaryChain v) =
      (D.cell v).boundaryIntegral f
```
