# Local conservation law

**Local conservation law** (MF08.2) `∂ₜu + ∂ₓq = s` at the point `(t, x)`, for a density
`u`, a flux `q` (positive towards increasing `x`) and a source `s`, each a function of time
and then space. The partial derivatives are Mathlib `deriv`s, so the predicate carries meaning
together with the differentiability hypotheses, which the lemmas state separately.
