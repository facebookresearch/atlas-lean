# Statement of the local Hopf bifurcation theorem on ℝᴺ

For `N ∈ ℕ`, the proposition that the classical local Hopf theorem (Hopf 1942; Marsden–McCracken)
holds on `ℝᴺ` in the following form. Let `F : ℝ × ℝᴺ → ℝᴺ`, an open set `U ⊆ ℝ × ℝᴺ`, a branch
`x_e : ℝ → ℝᴺ`, a curve `λ : ℝ → ℂ`, `λ' ∈ ℂ` and real `μ₀`, `ω₀` satisfy:

- `(μ₀, x_e(μ₀)) ∈ U` and `(μ, x) ↦ F(μ, x)` is infinitely differentiable on `U`;
- `x_e` is continuous at `μ₀`, and `F(μ, x_e(μ)) = 0` for all `μ` near `μ₀`;
- `ω₀ > 0`, and `iω₀` is a root of multiplicity `1` of the
  [characteristic polynomial of the linearization](lin-charpoly.md) of `F(μ₀, ·)` at `x_e(μ₀)`;
- every root of that polynomial with zero real part is `iω₀` or `−iω₀`;
- for all `μ` near `μ₀`, `λ(μ)` is a root of the characteristic polynomial of the linearization of
  `F(μ, ·)` at `x_e(μ)`; `λ(μ₀) = iω₀`; and `λ` has derivative `λ'` at `μ₀` with `Re λ' ≠ 0`.

Then for every `ε > 0` there are a parameter `μ` with `|μ − μ₀| < ε`, a period `T > 0` with
`|T − 2π/ω₀| < ε` and a solution `γ : ℝ → ℝᴺ` of `γ' = F(μ, γ)` on all of `ℝ` that is `T`-periodic,
not constant, and stays within `ε` of `x_e(μ₀)` in the maximum distance. Results that use it take
it as a hypothesis.
