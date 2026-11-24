# Markov family for a kernel family

Let `κ = (κ_t)_{t ≥ 0}` be a family of kernels on `[0, 1]`, `μ` a measure on a measurable space `Ω`,
`(𝒢_u)_{u ≥ 0}` a filtration and `Y` a process with values in `[0, 1]`. Then `Y` is a Markov family
for `κ` with respect to `(𝒢_u)` under `μ` if each `Y_u` is `𝒢_u`-measurable and, for all times
`0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every continuous `g : [0, 1] → ℝ`,
`∫_A g(Y_v) dμ = ∫_A ∫ g(y) κ_{v - u}(Y_u, dy) dμ`. These are real integrals, the integral of a
non-integrable function being `0`. If the kernels are Markov and `μ` is finite, all these integrals
are genuine finite integrals; the definition assumes neither, and the results on the families after
a deterministic time or a stopping time do not assume Markov kernels.
