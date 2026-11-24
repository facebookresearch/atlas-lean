# Rankine–Hugoniot condition from classical solutions on both sides

Let `f : ℝ → ℝ` be a flux, `s : ℝ → ℝ` an interface with derivative `c` at time `t`, and
`a < s(t) < b`. Let `u_L`, `v_L : ℝ² → ℝ` (fields of `(τ, x)`) and an open set `U_L` containing
`{t} × [a, s(t)]` be such that `u_L` is continuous on `U_L`, has time derivative `v_L` at every
point of `U_L`, with `v_L` continuous on `U_L`; and symmetrically `u_R`, `v_R` and an open
`U_R ⊇ {t} × [s(t), b]`. Suppose moreover that at time `t`:

- `y ↦ f(u_L(t, y))` is continuous on `[a, s(t)]` and has derivative `g_L(x)` at every
  `x ∈ (a, s(t))`, with `v_L(t, x) + g_L(x) = 0` there;
- symmetrically on `[s(t), b]` and `(s(t), b)` for `u_R`, with `v_R(t, x) + g_R(x) = 0`.

Then the split mass `τ ↦ ∫_a^{s(τ)} u_L(τ, x) dx + ∫_{s(τ)}^b u_R(τ, x) dx` has derivative
`f(u_L(t, a)) - f(u_R(t, b))` at `t` (flux in at `a` minus flux out at `b`) if and only if
`c (u_R - u_L) = f(u_R) - f(u_L)` at `(t, s(t))`, the Rankine–Hugoniot jump condition. No existence
of such solutions is asserted.
