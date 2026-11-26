# Absolute Jacquet integral on the principal series of `GL₂(ℚ_p)`

Let `v` be a finite
place of `ℚ`, `F = ℚ_v`, and let `χ₀, χ₁ : Fˣ → ℂˣ` be characters trivial on the higher unit
groups `higherUnitsAt ℚ v (cχ i)`. Let `ϖ` have valuation `exp (-1)` and assume
`‖χ₀(ϖ)‖ < ‖χ₁(ϖ)‖`. Let `f` lie in `principalSeries2 v χ` and be right invariant under some open
subgroup, and let `w₀ = !![0, 1; 1, 0]`. Then, for the Borel σ-algebra on `F` and every additive
Haar measure `ν` on `F`, the integral `J(g) = ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν`

* is finite for every `g`;
* satisfies `J(unipotentGL2 x * g) = J(g)`;
* satisfies `J(diag(t₁, t₂) * g) = ‖χ₀(t₂)‖ ‖χ₁(t₁)‖ √(‖t₁‖ / ‖t₂‖) J(g)`;
* is bounded on the local level-one subgroup `AdelicLevel.localLevelOne (𝓞 ℚ) ℚ v ⊤`.
