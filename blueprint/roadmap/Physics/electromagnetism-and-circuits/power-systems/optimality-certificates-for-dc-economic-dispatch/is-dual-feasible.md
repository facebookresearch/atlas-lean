# Dual feasibility of a dispatch dual witness

For a network with rational susceptances `b`, generators at buses, a reference bus `r` and costs
`c`, rational prices `λ`, a reference multiplier `ρ` and bound multipliers `μ_hi`, `μ_lo`, `η_hi`,
`η_lo` are dual feasible when

- `μ_hi`, `μ_lo`, `η_hi` and `η_lo` are nonnegative;
- `λ_v(g) = c_g + μ_hi,g - μ_lo,g` for every generator `g` at bus `v(g)` (the price at a generator's
  bus is its marginal cost corrected by its bound multipliers);
- `L_bᵀ λ + ρ e_r + (diag(b) Bᵀ)ᵀ (η_hi - η_lo) = 0` (angle stationarity), with `L_b` the
  [rational weighted Laplacian](rat-laplacian.md), `diag(b) Bᵀ` the
  [rational branch-flow matrix](rat-branch-flow-matrix.md) and `e_r` the indicator of `r`.
