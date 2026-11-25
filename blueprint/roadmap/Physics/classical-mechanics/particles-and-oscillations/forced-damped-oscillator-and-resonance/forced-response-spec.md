# For D ≠ 0, the forced response solves the equation with its data

Let `m > 0`, `c ≥ 0` and `k > 0`, let `F` and `Ω` be real numbers with nonzero
[steady-state denominator](steady-state-denominator.md) `D = (k - m Ω²)² + (c Ω)²`, and let `x₀`
and `v₀` be real numbers. Then the [forced response](forced-response.md) `x`:

- is twice continuously differentiable;
- satisfies `m x''(t) + c x'(t) + k x(t) = F cos (Ω t)` at every time `t`;
- has `x(0) = x₀` and `x'(0) = v₀`.
