# Effusion rate eq iff

Equal effusion rates at fixed number density (CH08.4): under the model hypothesis of
`effusion_rate_eq` for each gas, with its own factor
(`rate₁ = k₁ * meanSpeed R T₁ M₁`, `rate₂ = k₂ * meanSpeed R T₂ M₂`), and with `k₁ > 0` and
`hk : k₁ = k₂`, `rate₁ = rate₂ ↔ T₁ / M₁ = T₂ / M₂`; equal rates need the temperature ratio to
compensate the molar-mass ratio. As in `effusion_rate_ratio`, `k` packages the hole area, the
number density and the flow regime, which the model does not resolve, so `hk` is the formal
content of "same hole, same number density, molecular flow"; the model holds `k` fixed as the
temperature changes. This is not a fixed-pressure criterion: at fixed pressure the number
density, and hence `k`, would vary as `1 / T`, and equal fixed-pressure rates would instead
require `M₁ * T₁ = M₂ * T₂`.
