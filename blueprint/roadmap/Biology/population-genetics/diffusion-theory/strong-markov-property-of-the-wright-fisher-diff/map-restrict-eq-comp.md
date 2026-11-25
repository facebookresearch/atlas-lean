# Kernel form of the Markov property

Let `μ` be a finite measure on a measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family](is-neutral-markov-family.md) for the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md) `T`
with respect to `(𝒢_u)` under `μ`: each `Y_u` is a `𝒢_u`-measurable map into `[0, 1]`, and
`∫_A g(Y_v) dμ = ∫_A (T_{v - u} g)(Y_u) dμ` for all times `0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every
continuous `g : [0, 1] → ℝ`. For all times `0 ≤ u ≤ v` and every `A ∈ 𝒢_u`, the image of `μ|_A`
under `Y_v` is `∫ K_{v - u}(y, ·) ν(dy)`, where `ν` is the image of `μ|_A` under `Y_u` and `K` is
the
[neutral Wright–Fisher kernel](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md).
Here `μ|_A` is the restriction of `μ` to `A`; an image measure of `μ|_A` has total mass `μ(A)` and
is not normalized (it is the zero measure when `μ(A) = 0`).
