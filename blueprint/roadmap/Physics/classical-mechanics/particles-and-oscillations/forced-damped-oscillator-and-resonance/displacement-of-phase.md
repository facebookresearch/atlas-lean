# A phase-space solution gives a C² solution of the forced equation

Let `m > 0`, let `c`, `k`, `F` and `Ω` be real numbers, and let `z : ℝ → ℝ × ℝ` have derivative
`L z(t) + b(t)` at every time `t`, with the [phase-space operator](phase-operator.md) `L` and the
[phase-space forcing](phase-forcing.md) `b`. Then its first component `x = z₁`:

- is twice continuously differentiable, with derivative the second component: `x' = z₂`;
- satisfies `m x''(t) + c x'(t) + k x(t) = F cos (Ω t)` at every time `t`.
