/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.ZeroFreeRegion

/-!
# Tests for zero-free regions

The positivity of the zero terms at a boundary point, the optimisation step at concrete constants,
and the exceptional-zero statements for real characters.
-/

@[expose] public section

namespace ZeroFreeRegionTest

/-- `Re (1 / (s - ρ) + 1 / ρ) ≥ 0` at `s = 1`, `ρ = 1/2`: here it is `2 + 2 = 4`. -/
example : 0 ≤ (1 / ((1 : ℂ) - 1 / 2) + 1 / (1 / 2 : ℂ)).re :=
  Complex.re_one_div_sub_add_one_div_nonneg (by norm_num) (by norm_num) (by norm_num)

/-- The boundary `ρ = 0` is allowed (junk `1 / 0 = 0`). -/
example (s : ℂ) (hs : 1 ≤ s.re) : 0 ≤ (1 / (s - 0) + 1 / (0 : ℂ)).re :=
  Complex.re_one_div_sub_add_one_div_nonneg le_rfl zero_le_one hs

/-- The `4/3` optimisation step, as used in the de la Vallée Poussin argument. -/
example : ∃ c > 0, ∀ L β : ℝ, 1 ≤ L → β ≤ 1 →
    (∀ σ : ℝ, 1 < σ → σ ≤ 2 → 4 / (σ - β) < 3 / (σ - 1) + 1 * L) → β < 1 - c / L :=
  lt_one_sub_div_of_forall_div_sub_lt (by norm_num) (by norm_num) one_pos

/-- At most one exceptional zero, and it is real and simple. -/
example : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    χ ^ 2 = 1 → ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 →
      1 - c / Real.log (q * (|s.im| + 2)) < s.re →
        s.im = 0 ∧ analyticOrderAt (DirichletCharacter.LFunction χ) s = 1 := by
  obtain ⟨c₁, hc₁, h₁⟩ := DirichletCharacter.im_eq_zero_of_LFunction_eq_zero_of_sq_eq_one
  obtain ⟨c₂, hc₂, h₂⟩ := DirichletCharacter.analyticOrderAt_LFunction_eq_one_of_sq_eq_one
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun q _ χ hχ hχ2 s hs hre => ?_⟩
  have hlog : 0 ≤ Real.log (q * (|s.im| + 2)) := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact Real.log_nonneg (by nlinarith [abs_nonneg s.im])
  have hle : ∀ c, min c₁ c₂ ≤ c →
      1 - c / Real.log (q * (|s.im| + 2)) ≤ 1 - min c₁ c₂ / Real.log (q * (|s.im| + 2)) :=
    fun c hc => sub_le_sub_left (div_le_div_of_nonneg_right hc hlog) 1
  exact ⟨h₁ q χ hχ hχ2 s hs ((hle c₁ (min_le_left _ _)).trans_lt hre),
    h₂ q χ hχ hχ2 s hs ((hle c₂ (min_le_right _ _)).trans_lt hre)⟩

/-- The classical bound `-Re ζ'/ζ(s) < Re (1/(s-1)) + c log (|t| + 2)` at `s = 2`. -/
example : ∃ c₁ > 0, -(deriv riemannZeta 2 / riemannZeta 2).re <
    (1 / ((2 : ℂ) - 1)).re + c₁ * Real.log (|(2 : ℂ).im| + 2) := by
  obtain ⟨c₁, hc₁, h⟩ := exists_neg_re_logDeriv_riemannZeta_lt_re_one_div_sub_one_add_log
  exact ⟨c₁, hc₁, h 2 (by norm_num)⟩

end ZeroFreeRegionTest
