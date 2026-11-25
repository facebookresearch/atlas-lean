# Mass balance of the linear one-compartment model

For all real `k` and `R`, let `A` be differentiable at every time `t ≥ 0` with
`A'(t) = R - k * A(t)`, a solution of the one-compartment equation with elimination rate `k` and
constant input `R`. Then for every `t ≥ 0`, `A(t) + ∫₀ᵗ k * A(s) ds = A(0) + R * t`. In the model,
with `k ≥ 0`, `R ≥ 0` and `A(0) ≥ 0`, this reads: the amount present plus the amount eliminated
equals the initial amount plus the amount infused.
