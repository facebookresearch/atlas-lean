# Linearization type of a FitzHugh–Nagumo equilibrium

For real `b`, `ε` and `v`, the type is the trace–determinant classification of the
[Jacobian](jacobian.md) at voltage `v`, with the [trace](jac-trace.md) `τ = 1 - v² - ε b` and the
[determinant](jac-det.md) `Δ = ε (1 - b + b v²)`:

- saddle if `Δ < 0`;
- degenerate if `Δ = 0`;
- center if `Δ > 0` and `τ = 0`;
- stable node if `Δ > 0`, `τ < 0` and `4 Δ ≤ τ²`;
- stable focus if `Δ > 0`, `τ < 0` and `τ² < 4 Δ`;
- unstable node if `Δ > 0`, `τ > 0` and `4 Δ ≤ τ²`;
- unstable focus if `Δ > 0`, `τ > 0` and `τ² < 4 Δ`.

The definition takes any voltage `v`. For `b ≠ 0` and `ε ≠ 0`, which includes the model's domain
`b, ε > 0`, the voltage of an [equilibrium](is-equilibrium.md) is a root of the
[equilibrium cubic](eq-cubic.md) ([equilibria](is-equilibrium-iff.md)), so the type at an
equilibrium depends on `a`, `b` and `I` too. This needs both conditions: at `ε = 0`, for instance,
every point of the voltage nullcline is an equilibrium.
