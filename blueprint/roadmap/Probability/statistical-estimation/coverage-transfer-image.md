# Coverage of a confidence set transfers to its image under a map

Let `μ` be a probability measure on a measurable space `Ω`. For each outcome `ω`, let `S(ω)` be a
set of latent values and `T(ω)` a set of outputs, let `z(ω)` be the latent value, and let `g` map
latent values to outputs so that `z(ω) ∈ S(ω)` implies `g(z(ω)) ∈ T(ω)` for every `ω`. If `S` covers
`z` with probability at least `1 - α`, that is `μ {ω | z(ω) ∈ S(ω)} ≥ 1 - α` for a real number `α`,
then `T` covers `g(z)` with probability at least `1 - α`: `μ {ω | g(z(ω)) ∈ T(ω)} ≥ 1 - α`. No
measurability is assumed: on a set that is not measurable `μ` is the outer measure, and the second
event contains the first.
