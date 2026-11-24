# Linearization type of a FitzHugh–Nagumo equilibrium

For real `b`, `ε` and `v`, the type is the trace–determinant classification of the
[Jacobian](jacobian.md) at voltage `v`, with `τ = 1 - v² - ε b` and `Δ = ε (1 - b + b v²)`:

- saddle if `Δ < 0`;
- degenerate if `Δ = 0`;
- center if `Δ > 0` and `τ = 0`;
- stable node if `Δ > 0`, `τ < 0` and `4 Δ ≤ τ²`;
- stable focus if `Δ > 0`, `τ < 0` and `τ² < 4 Δ`;
- unstable node if `Δ > 0`, `τ > 0` and `4 Δ ≤ τ²`;
- unstable focus if `Δ > 0`, `τ > 0` and `τ² < 4 Δ`.

The definition takes any voltage `v`; at an [equilibrium](is-equilibrium.md) `v` is a root of the
[equilibrium cubic](eq-cubic.md), so it depends on `a`, `b` and `I` too.
