# Orthogonal estimation error gives equal cross and score terms

Let `μ` be a measure on a measurable space `Ω` and let `β = (β_1, …, β_M)` and
`β̂ = (β̂_1, …, β̂_M)` be real functions on `Ω` (true and estimated effects), square integrable with
respect to `μ`. If the estimation error is orthogonal in `L²(μ)` to every coordinate of `β̂`,

`∫ (β_k - β̂_k) β̂_l dμ = 0` for all `k, l`,

then `C_S(β, β̂) = C_S(β̂, β̂)` for every real `M × M` matrix `S`, where `C_S` is the
[training integral of the target cross moment](quad-cov.md).
