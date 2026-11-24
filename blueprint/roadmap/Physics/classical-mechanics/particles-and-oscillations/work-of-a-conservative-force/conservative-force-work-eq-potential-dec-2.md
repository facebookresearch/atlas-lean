# Conservative force work eq potential decrease

Work of a conservative force along an admissible path equals the
potential decrease: if `F = -g` where `g` is the gradient field of `U`
(`HasGradientAt U (g x) x`), `γ` is differentiable on `[a, b]` with
derivative `γ'`, and the work integrand is interval-integrable, then
`∫ t in a..b, ⟪F (γ t), γ' t⟫ = -(U (γ b) - U (γ a))`. The space is
complete because Mathlib's `HasGradientAt` requires it; see
`conservative_force_work_eq_potential_decrease_of_hasFDerivAt` for the
general form.
