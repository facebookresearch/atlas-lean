# Multi-time law of a Markov family

Let `μ` be a finite measure on a measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family](is-neutral-markov-family.md) for the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md) `T`
with respect to `(𝒢_u)` under `μ`: each `Y_u` is a `𝒢_u`-measurable map into `[0, 1]`, and
`∫_A g(Y_v) dμ = ∫_A (T_{v - u} g)(Y_u) dμ` for all times `0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every
continuous `g : [0, 1] → ℝ`. Let `t = (t_1, …, t_n)` be times with `t_1 ≤ ⋯ ≤ t_n`, let `s ≥ 0` with
`s ≤ t_i` for every `i`, and let `A ∈ 𝒢_s`. Then the image of `μ|_A` under `(Y_{t_1}, …, Y_{t_n})`
is `∫ Q_{s, t}(y, ·) ν(dy)`, where `ν` is the image of `μ|_A` under `Y_s` and `Q` is the
[finite-dimensional kernel](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/finite-chain-kernel.md)
of the
[neutral Wright–Fisher kernels](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md).
Here `μ|_A` is the restriction of `μ` to `A`; an image measure of `μ|_A` has total mass `μ(A)` and
is not normalized (it is the zero measure when `μ(A) = 0`).
