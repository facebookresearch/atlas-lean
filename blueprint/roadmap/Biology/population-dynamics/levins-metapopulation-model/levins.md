# Explicit solution of the Levins equation

For real numbers `c`, `e`, `p₀` and `t`, the explicit solution of the Levins equation with initial
value `p₀` is `p(t) = p₀ e^{(c - e) t} / (1 + c p₀ φ(t))`, where `φ(t) = ∫₀ᵗ e^{(c - e) s} ds`, that
is `φ(t) = (e^{(c - e) t} - 1) / (c - e)` for `c ≠ e` and `φ(t) = t` for `c = e`. A quotient with
denominator `0` is read as `0`. It is the
[explicit SIS solution](../../epidemiology/sis-epidemic-model/sis-infected.md) for the infectives
with `β = c`, `γ = e` and `N = 1`, and `p(0) = p₀` for all `c`, `e` and `p₀`. The intended domain is
`c ≥ 0`, `p₀ ≥ 0` and `t ≥ 0`: there the denominator is at least `1`, and `p`
[solves the Levins equation](is-solution-levins.md).
