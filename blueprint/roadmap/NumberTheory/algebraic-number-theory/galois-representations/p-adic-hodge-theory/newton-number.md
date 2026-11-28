# Newton Number

The Newton number `t_N(D)` of a finite-dimensional `(φ, N)`-module `M` on `D`, with respect to
an additive valuation `v : AddValuation K₀ (WithTop ℤ)`: the value under `v` of the determinant of
the matrix of `φ` in the basis `Module.finBasis K₀ D`. This determinant is nonzero, so its value
is an integer (`PhiNModule.coe_newtonNumber_finBasis`), and the default value `0` of
`WithTop.untopD` is never used. If `v (σ x) = v x` for all `x`, then any other basis gives the
same value (`PhiNModule.coe_newtonNumber`).
