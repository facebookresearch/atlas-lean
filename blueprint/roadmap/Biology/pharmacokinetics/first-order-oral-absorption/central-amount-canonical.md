# Canonical central amount for all rates

For a bioavailability `F`, a dose `D`, an absorption rate `ka`, an elimination rate `k` and a time
`t` (real numbers), the canonical central amount is the relaxation solution with elimination rate
`k`, input `F * ka` times the [depot amount](depot-amount.md) and initial value `0`:
`Ac(t) = ∫₀ᵗ exp (-k * (t - s)) * (F * ka * D * exp (-ka * s)) ds`, an oriented integral for
`t < 0`. It needs no distinct-rate condition: it is the
[distinct-rate closed form](central-amount-canonical-eq-distinct.md) when `ka ≠ k` and the
[equal-rate closed form](central-amount-canonical-eq-equal.md) when `ka = k`. The intended domain is
`0 ≤ F ≤ 1`, `D ≥ 0`, `ka > 0`, `k ≥ 0` and `t ≥ 0`.
