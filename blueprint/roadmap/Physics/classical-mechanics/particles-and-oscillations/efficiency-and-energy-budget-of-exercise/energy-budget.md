# Stored energy changes by the integrated net intake

Let `ρ_F > 0` and `ρ_L > 0` be energy densities, `t ≥ 0` a time, and `F`, `L`, `q_F`, `q_L`, `I`
and `X` real functions of time (two stores, two component fluxes, the intake and the
expenditure) such that, at every `s ∈ [0, t]`:

- `u ↦ ρ_F F(u)` has derivative `q_F(s)` at `s`, and `u ↦ ρ_L L(u)` has derivative `q_L(s)` at
  `s` (two-sided derivatives, also at `s = 0` and `s = t`);
- the net balance holds: `q_F(s) + q_L(s) = I(s) - X(s)`.

If moreover `I - X` is integrable on `[0, t]`, the stored energy `E = ρ_F F + ρ_L L` satisfies

`E(t) - E(0) = ∫₀ᵗ (I(s) - X(s)) ds`.

The densities are fixed numbers: the declared model has no variable-density or hydration term.
