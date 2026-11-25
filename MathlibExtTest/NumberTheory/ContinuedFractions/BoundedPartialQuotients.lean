/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ContinuedFractions.BoundedPartialQuotients
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.Translations

open GenContFract MetaMathlibExt

-- The expansion of 1/√17 - 1 starts [-1; 4, …]. At N = 0 and M = 3, the unreduced
-- fraction -2/2 represents the zeroth convergent and has the largest allowed denominator.
example : 1 / 24 < |(Real.sqrt 17)⁻¹ - 1 - (-2 : ℝ) / 2| := by
  let x := (Real.sqrt 17)⁻¹ - 1
  have hirr : Irrational (Real.sqrt 17) := by
    simpa using (show Nat.Prime 17 by decide).irrational_sqrt
  have hx : Irrational x := by simpa [x] using hirr.inv.sub_intCast 1
  have hs : 4 < Real.sqrt 17 ∧ Real.sqrt 17 < 5 := by
    constructor <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]
  have hinv : 0 < (Real.sqrt 17)⁻¹ := by positivity
  have hlt : (Real.sqrt 17)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [hs.1])
  have hfloor : ⌊x⌋ = -1 := Int.floor_eq_iff.mpr (by
    dsimp [x]
    norm_num
    grind)
  have hfract : Int.fract x = (Real.sqrt 17)⁻¹ := by simp [Int.fract, hfloor, x]
  have hdigit : (GenContFract.of x).s.get? 0 = some ⟨1, 4⟩ := by
    have ht : ⌊Real.sqrt 17⌋ = 4 := Int.floor_eq_iff.mpr (by norm_num; exact ⟨hs.1.le, hs.2⟩)
    change (GenContFract.of x).s.head = _
    simpa [hfract, ht] using of_s_head (v := x) (hfract ▸ hinv.ne')
  have hden := first_den_eq hdigit
  have ha (j : ℕ) (hj : j ≤ 0) (b : ℝ) (hb : (GenContFract.of x).partDens.get? j = some b) :
      b ≤ 4 := by
    obtain rfl := Nat.eq_zero_of_le_zero hj
    rw [partDen_eq_s_b hdigit] at hb
    exact (Option.some.inj hb).symm.le
  have h := one_div_partialQuotient_bound_lt_abs_sub hx (M := 3) (N := 0) (aM := 4)
    (p := -2) (q := 2) (by decide) (by norm_num) (by norm_num [hden])
    (by norm_num [hfloor]) ha (by decide) (by decide)
  norm_num [x] at h ⊢
  exact h
