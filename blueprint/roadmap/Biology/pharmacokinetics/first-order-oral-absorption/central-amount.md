# Central amount at distinct absorption and elimination rates

For a bioavailability `F`, a dose `D`, an absorption rate `ka`, an elimination rate `k` and a time
`t` (real numbers), the central amount at distinct rates is
`Ac(t) = F * D * ka * (exp (-k * t) - exp (-ka * t)) / (ka - k)`. It is defined for all real inputs;
with the convention `x / 0 = 0` it is `0` when `ka = k`, where the
[equal-rate central amount](central-amount-equal.md) `F * D * ka * t * exp (-ka * t)` is the right
formula. The intended domain is `ka ≠ k` with `0 ≤ F ≤ 1`, `D ≥ 0`, `ka > 0`, `k ≥ 0` and `t ≥ 0`.
