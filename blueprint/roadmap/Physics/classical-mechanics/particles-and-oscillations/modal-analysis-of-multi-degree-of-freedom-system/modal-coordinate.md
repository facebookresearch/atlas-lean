# Response of one modal coordinate

For real numbers `μ`, `q₀`, `v₀` and a time `t`, the modal response is

- `q(t) = q₀ cos (√μ t) + (v₀ / √μ) sin (√μ t)` when `μ > 0`, an oscillation at the modal angular
  frequency `√μ`;
- `q(t) = q₀ + v₀ t` when `μ ≤ 0`, the rigid drift.

It is meant for `μ ≥ 0`, where it solves `q'' + μ q = 0` with `q(0) = q₀` and `q'(0) = v₀`
([solution](modal-coordinate-solves.md)); for `μ < 0` the drift formula solves that equation only
when `q₀ = v₀ = 0`.
