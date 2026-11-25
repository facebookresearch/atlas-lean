# To Cycle integral

In a complete complex normed target, the filling-cycle integral is the sum of its selected cell
boundary integrals.

```lean
theorem toCycle_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f
```
