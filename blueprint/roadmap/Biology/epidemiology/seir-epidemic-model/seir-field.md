# The SEIR vector field on ℝ⁴

For real parameters `β`, `σ`, `γ` and `N`, the closed SEIR vector field on `ℝ⁴`, with coordinates
`(S, E, I, R)`, is

`f(S, E, I, R) = (-β S I / N, β S I / N - σ E, σ E - γ I, γ I)`,

where `β S I / N` is read as `0` when `N = 0`, the field then being the linear map
`(S, E, I, R) ↦ (0, -σ E, σ E - γ I, γ I)`; the intended domain is `N > 0`. The field also takes a
time argument, which it ignores: it is autonomous.
