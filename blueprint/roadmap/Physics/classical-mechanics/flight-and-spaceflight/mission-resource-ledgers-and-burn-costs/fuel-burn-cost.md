# Fuel consumption follows the delta-v cost, not the net change

Let `fuel : ℝ → ℝ → ℝ` be a supplied consumed-fraction functional (`fuel ve Δv` is the fraction of a
burn's initial mass consumed by a burn of delta-v `Δv` at the exhaust speed `ve`), and fix a real
`ve` with `fuel ve 0 = 0` and `(1 − fuel ve d₁)(1 − fuel ve d₂) = 1 − fuel ve (d₁ + d₂)` for all
real `d₁`, `d₂`, and with `fuel ve` nondecreasing in delta-v. For a seminormed additive commutative
group `E`, burns `Δv : ℕ → E`, `n ∈ ℕ` and a budget `B`: the burns consume
`1 − ∏_{k < n} (1 − fuel ve ‖Δv_k‖) = fuel ve (C)`, where `C` is the [delta-v cost](burn-cost.md)
`∑_{k < n} ‖Δv_k‖`; the net change would give at most as much,
`fuel ve ‖∑_{k < n} Δv_k‖ ≤ fuel ve (C)`; and if `C ≤ B`, the consumed fraction is at most
`fuel ve B`. No sign condition on `ve` is needed.
