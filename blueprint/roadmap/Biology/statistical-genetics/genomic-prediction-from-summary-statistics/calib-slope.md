# Calibration slope of a polygenic score

Let `μ` be a measure on a measurable space `Ω`, let `S` be a real `M × M` matrix (the target LD
matrix), and let `β = (β_1, …, β_M)` and `β̂ = (β̂_1, …, β̂_M)` be real functions on `Ω` (true and
estimated effects). The calibration slope of the score `xᵀ β̂` is

`C_S(β, β̂) / C_S(β̂, β̂)`,

where `C_S` is the [training integral of the target cross moment](quad-cov.md), with the convention
`x / 0 = 0`: it is `0` when `C_S(β̂, β̂) = 0`. It is the ratio of the training integrals of the
numerator `βᵀ S β̂` and the denominator `β̂ᵀ S β̂` of the slope of the regression of the target
phenotype (equally, of the genetic value `xᵀ β`) on the score. A score is calibrated when its
calibration slope is `1`.
