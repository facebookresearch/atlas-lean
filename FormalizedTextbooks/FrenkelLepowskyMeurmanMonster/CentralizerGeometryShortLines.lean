/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual Leech short labels determine distinct physical real lines. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The physical short vectors are nonzero, with their actual squared length four. -/
theorem centralizer_shortVector_ne_zero (r : GriessShortIndex) : griessShortVector r ≠ 0 := by
  intro h
  have hn := griessShortVector_norm_sq r
  simp only [h, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hn
  norm_num at hn

/-- Equality up to global sign of physical vectors identifies the actual short label. -/
theorem centralizer_shortVector_sign_unique (r s : GriessShortIndex)
    (h : griessShortVector r = griessShortVector s ∨
      griessShortVector r = -griessShortVector s) : r = s := by
  apply griessShort_label_unique
  have hs : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rcases h with h | h
  · left
    funext i
    have hi := congrFun h i
    change (griessShortIntegral r i : ℝ) / Real.sqrt 8 =
      (griessShortIntegral s i : ℝ) / Real.sqrt 8 at hi
    exact Int.cast_injective ((div_left_inj' hs).mp hi)
  · right
    funext i
    have hi := congrFun h i
    change (griessShortIntegral r i : ℝ) / Real.sqrt 8 =
      -((griessShortIntegral s i : ℝ) / Real.sqrt 8) at hi
    rw [← neg_div] at hi
    have hz := (div_left_inj' hs).mp hi
    exact_mod_cast hz

/-- Any scalar identification of two actual short vectors has scalar one or minus one. -/
theorem centralizer_shortVector_scalar_sign (r s : GriessShortIndex) (t : ℝ)
    (h : griessShortVector r = t • griessShortVector s) : t = 1 ∨ t = -1 := by
  have hn := griessShortVector_norm_sq r
  simp only [h, Pi.smul_apply, smul_eq_mul] at hn
  have he (i : Fin 24) :
      (t * griessShortVector s i) * (t * griessShortVector s i) =
        t ^ 2 * (griessShortVector s i * griessShortVector s i) := by ring
  simp_rw [he] at hn
  rw [← Finset.mul_sum, griessShortVector_norm_sq] at hn
  have ht : t ^ 2 = 1 := by nlinarith
  exact sq_eq_one_iff.mp ht

/-- Distinct labels cannot lie on the same physical short-vector line. -/
theorem centralizer_shortVector_line_unique (r s : GriessShortIndex) (t : ℝ)
    (h : griessShortVector r = t • griessShortVector s) : r = s := by
  rcases centralizer_shortVector_scalar_sign r s t h with ht | ht
  · apply centralizer_shortVector_sign_unique r s
    left
    simpa only [ht, one_smul] using h
  · apply centralizer_shortVector_sign_unique r s
    right
    simpa only [ht, neg_one_smul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
