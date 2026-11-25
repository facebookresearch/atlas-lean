/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.GowersNorm

import Mathlib.Tactic

/-!
# Tests for Gowers uniformity norms

Non-vacuity checks: the hypotheses of the main statements are satisfiable on small groups, and
`U¹` is a seminorm only (a mean-zero function with `U¹ = 0` and `U² = 1`).
-/

open scoped BigOperators ComplexConjugate
open MathlibExt.Combinatorics.Additive.GowersNorm

namespace MathlibExtTest.Combinatorics.Additive.GowersNorm

/-- The sign character of `Fin 2`. -/
noncomputable def sgn : Fin 2 → ℂ := fun x => if x = 0 then 1 else -1

example : gowersNorm 1 (fun _ : ZMod 3 => (1 : ℂ)) = 1 := by
  rw [gowersNorm_one]; simp

/-- `U¹` vanishes on the mean-zero sign function. -/
example : gowersNorm 1 sgn = 0 := by
  rw [gowersNorm_one]
  simp [sgn, Fintype.expect_eq_sum_div_card, Fin.sum_univ_two]

/-- The sign function has `U²` power `1`, so `U¹` is not a norm. -/
example : gowersPow 2 sgn = 1 := by
  rw [gowersPow_two]
  simp only [Fintype.expect_eq_sum_div_card]
  simp [sgn, Fin.sum_univ_two]

/-- `|𝔼 f| ≤ ‖f‖_{U^d}` for `d ≥ 1`: here `1 ≤ ‖1‖_{U³}` on `ZMod 5`. -/
example : (1 : ℝ) ≤ gowersNorm 3 (fun _ : ZMod 5 => (1 : ℂ)) := by
  have := norm_expect_le_gowersNorm (fun _ : ZMod 5 => (1 : ℂ)) (d := 3) (by norm_num)
  simpa using this

/-- The generalized von Neumann theorem applies on `ZMod 3` (odd order). -/
example (f₀ f₁ f₂ : ZMod 3 → ℂ) (h₀ : ∀ x, ‖f₀ x‖ ≤ 1) (h₁ : ∀ x, ‖f₁ x‖ ≤ 1)
    (h₂ : ∀ x, ‖f₂ x‖ ≤ 1) : ‖apCountThree f₀ f₁ f₂‖ ≤ gowersNorm 2 f₁ :=
  (norm_apCountThree_le_gowersNorm_two (by decide) f₀ f₁ f₂ h₀ h₁ h₂).2.1

/-- The `U²` inverse theorem with `c = 1` applies to the constant function `1`. -/
example : ∃ ψ : AddChar (ZMod 3) ℂ, (1 : ℝ) ^ 2 ≤ ‖𝔼 x, (1 : ℂ) * conj (ψ x)‖ := by
  refine exists_character_correlation_of_le_gowersNorm_two (fun _ => (1 : ℂ)) (by simp)
    zero_le_one ?_
  have := norm_expect_le_gowersNorm (fun _ : ZMod 3 => (1 : ℂ)) (d := 2) (by norm_num)
  simpa using this

/-- Gowers–Cauchy–Schwarz (`d = 3`) and the triangle inequality, instantiated. -/
example (F : (Fin 3 → Bool) → ZMod 4 → ℂ) (f g : ZMod 4 → ℂ) :
    ‖gowersInner 3 F‖ ≤ ∏ ω, gowersNorm 3 (F ω) ∧
      gowersNorm 3 (f + g) ≤ gowersNorm 3 f + gowersNorm 3 g :=
  ⟨norm_gowersInner_le 3 F, gowersNorm_add_le 3 f g⟩

/-- The cube formula for `d = 1`: `gowersPow 1 f = 𝔼_{x,h} f(x) conj f(x + h)`. -/
example (f : ZMod 3 → ℂ) :
    gowersPow 1 f = 𝔼 x, 𝔼 h : Fin 1 → ZMod 3, ∏ ω : Fin 1 → Bool,
      (if Even (Finset.univ.filter fun i => ω i = true).card
        then f (x + ∑ i, if ω i then h i else 0)
        else conj (f (x + ∑ i, if ω i then h i else 0))) :=
  gowersPow_eq_cubeAverage 1 f

/-- The generalized von Neumann theorem for four-term progressions on `ZMod 5`
(`5` is coprime to `3! = 6`). -/
example (f : Fin 4 → ZMod 5 → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖𝔼 x, 𝔼 r, ∏ i : Fin 4, f i (x + (i : ℕ) • r)‖ ≤ gowersNorm 3 (f 2) :=
  norm_apCount_le_gowersNorm 4 (by norm_num) (by decide) f hf 2

end MathlibExtTest.Combinatorics.Additive.GowersNorm
