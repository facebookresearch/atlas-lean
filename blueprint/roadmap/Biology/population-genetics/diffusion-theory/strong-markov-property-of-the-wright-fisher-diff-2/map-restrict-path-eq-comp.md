# Path law of a Markov family

Let `κ = (κ_t)_{t ≥ 0}` be a family of Markov kernels on `[0, 1]`, `μ` a finite measure on a
measurable space `Ω`, `(𝒢_u)_{u ≥ 0}` a filtration and `Y` a
[Markov family for `κ`](is-kernel-markov-family.md) with respect to `(𝒢_u)` under `μ`: each `Y_u` is
a `𝒢_u`-measurable map into `[0, 1]`, and `∫_A g(Y_v) dμ = ∫_A ∫ g(y) κ_{v - u}(Y_u, dy) dμ` for all
times `0 ≤ u ≤ v`, every `A ∈ 𝒢_u` and every continuous `g : [0, 1] → ℝ`. Suppose moreover that `κ`
satisfies the Chapman–Kolmogorov equations `κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`. Then for
every `A ∈ 𝒢_0`, the image of `μ|_A` under the path `(Y_u)_{u ≥ 0}` is `∫ P^κ_y ν(dy)`, where `ν` is
the image of `μ|_A` under `Y_0` and `P^κ_y` is the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
of `κ` with input `y`. Here `μ|_A` is the restriction of `μ` to `A`; an image measure of `μ|_A` has
total mass `μ(A)` and is not normalized (it is the zero measure when `μ(A) = 0`). Here `y` is the
input of the kernel construction: the time-`0` marginal of `P^κ_y` is `κ_0(y, ·)`. This marginal is
the point mass at the input for every input exactly when `κ_0` is the identity kernel, which is not
assumed here; the Chapman–Kolmogorov equations alone do not imply it (the constant family
`κ_t(x, ·) = δ_0` satisfies them, and `κ_0(1, ·) = δ_0`).
