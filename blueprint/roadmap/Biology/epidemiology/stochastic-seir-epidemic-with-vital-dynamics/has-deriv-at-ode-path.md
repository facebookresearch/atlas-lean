# SEIR solutions solve the mass-action system of the network

Let `β`, `σ`, `γ`, `μ` be real and let `(s, e, i, r)` be a
[solution of the SEIR system with vital dynamics](../global-stability-of-the-seir-model/is-solution.md)
at scale `1` on `t ≥ 0`. Then at every `t ≥ 0` the [vector path](ode-path.md) `x = (s, e, i, r)` has
derivative `x'(t) = f(x(t))`, where `f` is the
[mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md) of the
[SEIR reaction network](network.md) with the [rate constants](rate-const.md)
`κ = (μ, β, σ, γ, μ, μ, μ, μ)`:

`f(x)_X = ∑_c κ_c (∏_Y x_Y^(src(c)_Y)) (prod(c)_X - src(c)_X)`.
