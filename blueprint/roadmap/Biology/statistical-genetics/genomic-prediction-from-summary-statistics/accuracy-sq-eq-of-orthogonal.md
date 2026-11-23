# Squared accuracy under orthogonal estimation error

Let `μ` be a measure on a measurable space `Ω`, let `S` be a real `M × M` matrix, and let
`β = (β_1, …, β_M)` and `β̂ = (β̂_1, …, β̂_M)` be real functions on `Ω` (true and estimated
effects), square integrable with respect to `μ`. If the estimation error is orthogonal in `L²(μ)` to
every coordinate of `β̂`,

`∫ (β_k - β̂_k) β̂_l dμ = 0` for all `k, l`,

and `C_S(β̂, β̂) ≠ 0`, then the [squared accuracy](accuracy-sq-2.md) of the score `xᵀ β̂` is

`C_S(β̂, β̂) / C_S(β, β)`,

with the convention `x / 0 = 0` (both sides are `0` when `C_S(β, β) = 0`). Here `C_S` is the
[training integral of the target cross moment](quad-cov.md): the squared accuracy is the ratio of
the score term to the genetic-value term.
