/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralPellBisectorsBisectorEquationFormTen

namespace MathlibExtTest.NumberTheory.GeneralPellBisectorsBisectorEquationFormTen

open MetaMathlibExt

-- At `n = 1` the triple is `(a, b, c) = (1, -7, 3)`.
example : ((1 : ℤ) - 3) ^ 2 * ((-7) ^ 2 + 1) = (-7 - 3) ^ 2 * (1 ^ 2 + 1) := by
  have hten := bisector_equation_form_ten 1 (by norm_num)
  dsimp only at hten
  simp only [show (2 * 1 - 1 : ℕ) = 1 from by omega,
    show (2 * 1 + 1 : ℕ) = 3 from by omega] at hten
  simp only [show (2 * 1 : ℕ) = 2 from by omega] at hten
  have hf1 : negPellF 2 1 = 1 := negPellF_two_one.1
  have hg1 : negPellG 2 1 = 1 := negPellF_two_one.2
  have hX : negPellFundX 2 = 1 := negPellFund_two.2
  have hY : negPellFundY 2 = 1 := negPellFund_two.1
  have hf2 : negPellF 2 2 = 3 := by
    have h := (negPell_succ 2 1).1
    rw [show (1 + 1 : ℕ) = 2 from by omega, hf1, hg1, hX, hY] at h
    norm_num at h
    exact h
  have hg2 : negPellG 2 2 = 2 := by
    have h := (negPell_succ 2 1).2
    rw [show (1 + 1 : ℕ) = 2 from by omega, hf1, hg1, hX, hY] at h
    norm_num at h
    exact h
  have hf3 : negPellF 2 3 = 7 := by
    have h := (negPell_succ 2 2).1
    rw [show (2 + 1 : ℕ) = 3 from by omega, hf2, hg2, hX, hY] at h
    norm_num at h
    exact h
  rw [hf1, hf2, hf3] at hten
  exact hten

end MathlibExtTest.NumberTheory.GeneralPellBisectorsBisectorEquationFormTen
