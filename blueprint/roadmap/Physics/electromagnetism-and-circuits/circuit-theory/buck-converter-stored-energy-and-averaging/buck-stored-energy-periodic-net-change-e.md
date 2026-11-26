# Zero net energy change of the buck converter over a returning horizon

Let `L > 0`, `C > 0`, `R > 0`, `Vin` and `T ≥ 0` be real numbers, `s, i, v : ℝ → ℝ` functions of
time and `0 = τ₀ < τ₁ < ⋯ < τ_n = T` switching instants, satisfying on `[0, T]` the hypotheses of
the [integrated energy balance](buck-stored-energy-sub-eq-integral-suppl.md): `i` and `v` continuous
on `[0, T]`; on each `(τ_k, τ_{k+1})`, `s` constant with value `0` or `1`, `i` and `v`
differentiable and `L i' = s Vin - v`, `C v' = i - v / R`; and `s Vin i - v² / R` integrable on
`[0, T]`. If `i(T) = i(0)` and `v(T) = v(0)`, then `E(T) - E(0) = 0` for the
[stored energy](buck-stored-energy.md) `E`, and `∫_0^T (s Vin i - v² / R) dt = 0`. One period of a
periodic steady state is the intended instance; periodicity enters only through the endpoint
equalities, and `T = 0` is allowed.
