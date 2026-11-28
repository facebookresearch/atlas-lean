# A C² solution of the forced equation gives a phase-space solution

Let `m > 0`, let `c`, `k`, `F` and `Ω` be real numbers, and let `x : ℝ → ℝ` be twice continuously
differentiable with `m x''(t) + c x'(t) + k x(t) = F cos (Ω t)` at every time `t`. Then at every
time `t` the curve `s ↦ (x(s), x'(s))` has derivative `L(x(t), x'(t)) + b(t)`, with the
[phase-space operator](phase-operator.md) `L(x, v) = (v, -(k / m) x - (c / m) v)` and the
[phase-space forcing](phase-forcing.md) `b(t) = (0, F cos (Ω t) / m)`.
