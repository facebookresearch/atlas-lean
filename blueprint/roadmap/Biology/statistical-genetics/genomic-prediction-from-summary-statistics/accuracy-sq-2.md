# Squared accuracy of a polygenic score for a target LD matrix

Let `μ` be a measure on a measurable space `Ω`, let `S` be a real `M × M` matrix (the target LD
matrix), and let `β = (β_1, …, β_M)` and `β̂ = (β̂_1, …, β̂_M)` be real functions on `Ω` (true and
estimated effects). The squared accuracy of the score `xᵀ β̂` for the genetic value `xᵀ β` is

`C_S(β, β̂)² / (C_S(β, β) C_S(β̂, β̂))`,

where `C_S` is the [training integral of the target cross moment](quad-cov.md), with the convention
`x / 0 = 0`: it is `0` when `C_S(β, β) C_S(β̂, β̂) = 0`. It is a ratio of training integrals of
target second moments, not the training integral of a squared correlation.
