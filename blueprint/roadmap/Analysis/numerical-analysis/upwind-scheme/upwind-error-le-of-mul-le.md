# Nodal error of the upwind scheme at a final time

Let `L > 0`, `Δt > 0`, `c₀`, `a` and `v` be real, `N_c ≥ 1` cells with `Δx = L / N_c` and Courant
number `0 ≤ ν = v Δt / Δx ≤ 1`, and `u` a sequence of grid functions on `ℤ/N_cℤ` with
`u^{k+1}_j = (1 - ν) u^k_j + ν u^k_{j-1}` for all `k` and `j`. With `E_k = max_j |u^k_j - w^k_j|`
for the [samples](sampled-wave.md) `w` and `M = |a| (2π / L)²`, for every `N` and every real `T`
with `N Δt ≤ T`, `E_N ≤ E_0 + T M (v² Δt + v Δx) / 2`. This is the
[N-step error bound](upwind-error-le.md) with `N Δt` replaced by `T`.
