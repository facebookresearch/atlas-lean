# Orthogonal error and a nonzero score term give calibration slope one

Let `μ` be a measure on a measurable space `Ω`, let `S` be a real `M × M` matrix, and let
`β = (β_1, …, β_M)` and `β̂ = (β̂_1, …, β̂_M)` be real functions on `Ω` (true and estimated
effects), square integrable with respect to `μ`. If the estimation error is orthogonal in `L²(μ)` to
every coordinate of `β̂`,

`∫ (β_k - β̂_k) β̂_l dμ = 0` for all `k, l`,

and `C_S(β̂, β̂) ≠ 0`, then the [calibration slope](calib-slope.md) `C_S(β, β̂) / C_S(β̂, β̂)` is
`1`. Here `C_S` is the [training integral of the target cross moment](quad-cov.md). The
orthogonality holds, for example, when `β̂` is the best linear predictor of `β` in `L²(μ)` from some
data (the orthogonal projection onto their span).
