/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ContinuedFractions.BestApproximation
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.NumberTheory.Real.GoldenRatio

namespace MetaMathlibExt

open GenContFract Real
open scoped goldenRatio

-- At the first admissible index, 3/2 beats both 2/1 and the unreduced competitor 4/2.
example : |3 - 2 * φ| < |2 - φ| ∧ |3 - 2 * φ| < |4 - 2 * φ| := by
  have hfloor : ⌊φ⌋ = 1 := Int.floor_eq_iff.mpr (by
    norm_num
    exact ⟨one_lt_goldenRatio.le, goldenRatio_lt_two⟩)
  have hfract : Int.fract φ = φ⁻¹ := by
    rw [Int.fract, hfloor, Int.cast_one, inv_goldenRatio]
    linarith [goldenRatio_add_goldenConj]
  have hstep (n : ℕ) : IntFractPair.stream φ (n + 1) = IntFractPair.stream φ n := by
    rw [IntFractPair.stream_succ (by rw [hfract]; exact inv_ne_zero goldenRatio_ne_zero),
      hfract, inv_inv]
  have hdigit (n : ℕ) (h : IntFractPair.stream φ (n + 1) = some (IntFractPair.of φ)) :
      (GenContFract.of φ).s.get? n = some ⟨1, 1⟩ := by
    simpa [IntFractPair.of, hfloor] using get?_of_eq_some_of_succ_get?_intFractPair_stream h
  have h₀ := hdigit 0 (hstep 0)
  have h₁ := hdigit 1 ((hstep 1).trans (hstep 0))
  have hc : (GenContFract.of φ).conts 2 = ⟨3, 2⟩ := by
    norm_num [conts_recurrence h₁ rfl (first_cont_eq h₀), of_h_eq_floor, hfloor]
  have hnum : (GenContFract.of φ).nums 2 = 3 := congrArg Pair.a hc
  have hden : (GenContFract.of φ).dens 2 = 2 := congrArg Pair.b hc
  constructor
  · simpa [hnum, hden] using abs_convergent_num_sub_lt_of_le_den goldenRatio_irrational
      (n := 2) (p := 2) (q := 1) (by decide) (by decide) (by norm_num [hden])
      (by norm_num [hnum, hden])
  · simpa [hnum, hden] using abs_convergent_num_sub_lt_of_le_den goldenRatio_irrational
      (n := 2) (p := 4) (q := 2) (by decide) (by decide) (by norm_num [hden])
      (by norm_num [hnum, hden])

end MetaMathlibExt
