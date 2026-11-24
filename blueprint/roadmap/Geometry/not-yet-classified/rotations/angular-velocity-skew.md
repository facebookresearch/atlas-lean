# Angular velocity skew

Angular-velocity matrix is skew-symmetric: if `R(t)` is orthogonal
(`R(t) * R(t)ᵀ = 1`) and every entry is differentiable at `t`, then the
matrix `W` with entries `W i j = ∑ k, R'(t) i k * R(t) j k` satisfies
`W i j = -W j i`. Here `R'` is the entrywise `deriv`.
