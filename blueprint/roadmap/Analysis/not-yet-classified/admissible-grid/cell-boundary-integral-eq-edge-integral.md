# Cell boundary Integral eq edge Integral

The boundary integral of one grid cell is the signed sum of its four
canonical grid-edge integrals.

```lean
theorem cell_boundaryIntegral_eq_edgeIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (v : GridIndex) (f : ℂ → E) :
    (D.cell v).boundaryIntegral f =
      D.edgeIntegral (.horizontal v) f -
        D.edgeIntegral (.horizontal (v.succ 1)) f +
          D.edgeIntegral (.vertical (v.succ 0)) f -
            D.edgeIntegral (.vertical v) f
```
