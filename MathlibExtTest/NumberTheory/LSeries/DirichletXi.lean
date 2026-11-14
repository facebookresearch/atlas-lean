/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.DirichletXi

/-!
# Tests for the completed Dirichlet `L`-function `ξ(s, χ)`

The normalisation of `DirichletCharacter.xi` (the factor `q ^ ((s + a) / 2)`, agreement with
`(q/π)^{(s+a)/2} Γ((s+a)/2) L(s, χ)` on `Re s > 0`, reduction to `Λ(s)` for `q = 1`), its
functional equation, and the satisfiability of the enumeration hypothesis of the Hadamard
product.
-/

@[expose] public section

open Complex DirichletCharacter

namespace DirichletXiTest

/-- The definition. -/
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    xi χ s = (q : ℂ) ^ ((s + (1 - χ (-1)) / 2) / 2) * completedLFunction χ s :=
  rfl

/-- For `q = 1`, `ξ(s, χ) = Λ(s)` is the completed Riemann zeta function (with poles at `0` and
`1`), not the entire Riemann `ξ`; this is why the analytic statements assume `χ ≠ 1`. -/
example (χ : DirichletCharacter ℂ 1) : xi χ = completedRiemannZeta := by
  ext s
  simp [xi, completedLFunction_modOne_eq]

/-- **Normalisation, even case.** For even `χ` mod `q ≠ 1` and `Re s > 0`,
`ξ(s, χ) = q^{s/2} Γℝ(s) L(s, χ) = (q/π)^{s/2} Γ(s/2) L(s, χ)`. -/
example {q : ℕ} [NeZero q] (hq : q ≠ 1) {χ : DirichletCharacter ℂ q} (he : χ.Even) {s : ℂ}
    (hs : 0 < s.re) : xi χ s = (q : ℂ) ^ (s / 2) * Gammaℝ s * LFunction χ s := by
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  rw [LFunction_eq_completed_div_gammaFactor χ s (.inr hq), he.gammaFactor_def, xi,
    show χ (-1) = 1 from he]
  field_simp
  ring_nf

/-- **Normalisation, odd case.** For odd `χ` and `Re s > 0`,
`ξ(s, χ) = q^{(s+1)/2} Γℝ(s + 1) L(s, χ)`. -/
example {q : ℕ} [NeZero q] (hq : q ≠ 1) {χ : DirichletCharacter ℂ q} (ho : χ.Odd) {s : ℂ}
    (hs : 0 < s.re) : xi χ s = (q : ℂ) ^ ((s + 1) / 2) * Gammaℝ (s + 1) * LFunction χ s := by
  have hG : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [LFunction_eq_completed_div_gammaFactor χ s (.inr hq), ho.gammaFactor_def, xi,
    show χ (-1) = -1 from ho]
  field_simp
  ring_nf

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) :
    Differentiable ℂ (xi χ) :=
  differentiable_xi hχ1

/-- The functional equation `ξ(1 - s, χ) = W(χ) ξ(s, χ⁻¹)`. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (s : ℂ) :
    xi χ (1 - s) = rootNumber χ * xi χ⁻¹ s :=
  xi_one_sub hχ s

/-- `ξ(s, χ)` vanishes exactly at the nontrivial zeros, and not at `0`. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    xi χ 0 ≠ 0 ∧ ∀ s, xi χ s = 0 ↔ s ∈ χ.nontrivialZeros :=
  ⟨xi_zero_ne_zero hχ hχ1, xi_eq_zero_iff hχ hχ1⟩

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) :
    Complex.HasGrowthOrder (xi χ) 1 :=
  hasGrowthOrder_xi hχ1

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    χ.nontrivialZeros.Infinite :=
  nontrivialZeros_infinite hχ hχ1

/-- The enumeration hypothesis for `ξ(s, χ)` is satisfiable (by the generic
`Complex.card_sigma_fin_analyticOrderAt`), so the Hadamard product can be instantiated. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∃ (ι : Type) (z : ι → ℂ) (A B : ℂ), (∀ s, xi χ s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n)) ∧
      Complex.exp A = xi χ 0 ∧ HasSum (fun n => (1 / z n).re) (-B.re) := by
  have hz := Complex.card_sigma_fin_analyticOrderAt (differentiable_xi hχ1)
    (xi_zero_ne_zero hχ hχ1)
  obtain ⟨A, B, h⟩ := exists_xi_eq_exp_mul_tprod hχ hχ1 hz
  exact ⟨_, _, A, B, h, exp_eq_xi_zero_of_xi_eq_exp_mul_tprod h,
    hasSum_re_one_div_of_xi_eq_exp_mul_tprod hχ hχ1 hz h⟩

/-- `‖L(k, χ)‖ ≥ 1/2` for `k ≥ 5`. -/
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (1 / 2 : ℝ) ≤ ‖LSeries (fun n : ℕ => χ n) 5‖ := by
  exact_mod_cast one_half_le_norm_LSeries_natCast χ (k := 5) le_rfl

end DirichletXiTest
