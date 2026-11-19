/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Externalities.Pigouvian
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Examples and checks for `MathlibExt.Economics.Externalities.Pigouvian` (Atlas AP02.T01). -/

namespace MathlibExtTest.Economics.Externalities.Pigouvian

open MathlibExt.Economics.Pigouvian

example : IsMaxOn
    (taxedSurplus (fun q : ℝ => 12 * q - q ^ 2) (fun q : ℝ => q ^ 2) 4)
    Set.univ 2 := by
  have h1 : HasDerivAt (fun q : ℝ => 12 * q) 12 2 := by
    have h := (hasDerivAt_id' (2 : ℝ)).const_mul 12
    simpa only [mul_one] using h
  have h2 : HasDerivAt (fun q : ℝ => q ^ 2) 4 2 := by
    have h := hasDerivAt_pow 2 (2 : ℝ)
    norm_num at h
    exact h
  have hB : HasDerivAt (fun q : ℝ => 12 * q - q ^ 2) 8 2 := by
    have h := h1.sub h2
    norm_num at h
    exact h
  have hopt : IsLocalMax
      (socialWelfare (fun q : ℝ => 12 * q - q ^ 2) (fun q : ℝ => q ^ 2)
        (fun q : ℝ => q ^ 2)) 2 := by
    refine Filter.Eventually.of_forall fun x => ?_
    show (12 * x - x ^ 2) - x ^ 2 - x ^ 2 ≤ (12 * 2 - 2 ^ 2) - 2 ^ 2 - 2 ^ 2
    nlinarith [sq_nonneg (x - 2)]
  have hconc : ConcaveOn ℝ Set.univ
      (taxedSurplus (fun q : ℝ => 12 * q - q ^ 2) (fun q : ℝ => q ^ 2) 4) := by
    constructor
    · exact convex_univ
    · intro x _ y _ a b ha hb hab
      simp only [taxedSurplus, smul_eq_mul]
      have hb1 : b = 1 - a := by linarith
      have h1a : (0:ℝ) ≤ 1 - a := by linarith
      have hnn := mul_nonneg (mul_nonneg ha h1a) (sq_nonneg (x - y))
      rw [hb1]
      nlinarith [hnn]
  exact isMaxOn_taxedSurplus_of_isLocalMax Filter.univ_mem hopt hB h2 h2 hconc

end MathlibExtTest.Economics.Externalities.Pigouvian
