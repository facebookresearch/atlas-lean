# A reversed torque sign breaks the planar rigid-body power balance

Let `E` be a real inner product space, `m > 0` and `J > 0`, `V, F : ℝ → E` and `θ, τ : ℝ → ℝ`, with
`V` continuously differentiable, `θ` twice continuously differentiable, and `m V'(s) = F(s)` and
`J θ''(s) = τ(s)` at every time `s`. If `τ(t) θ'(t) ≠ 0` at a time `t`, then the kinetic energy
`s ↦ m ‖V(s)‖² / 2 + J θ'(s)² / 2` does not have derivative `⟨F(t), V(t)⟩ - τ(t) θ'(t)` at `t`: its
[rate](planar-rigid-power-port.md) is `⟨F(t), V(t)⟩ + τ(t) θ'(t)`.
