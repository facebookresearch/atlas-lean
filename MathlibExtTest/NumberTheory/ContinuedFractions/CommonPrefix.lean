/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ContinuedFractions.CommonPrefix

open GenContFract
open GenContFract (of)
open MetaMathlibExt

-- At k = 0 only the integer parts are needed.
example (x y : ℝ) (h : ⌊x⌋ = ⌊y⌋) : |x - y| ≤ 2 := by
  simpa using abs_sub_le_of_contFrac_prefix_eq x y 0 (by simp [h]) (by simp)

-- The expansion [-1; 2, 2] stops at the shared convergent of [-1; 2, 2, 2].
example : |(-3 / 5 : ℝ) - (-7 / 12)| ≤ 1 / 2 := by
  have head (x : ℝ) (hx : Int.fract x ≠ 0) :
      (of x).s.get? 0 = some ⟨1, ⌊(Int.fract x)⁻¹⌋⟩ := of_s_head hx
  have hd : ∀ i < 2, (of (-3 / 5 : ℝ)).partDens.get? i =
      (of (-7 / 12 : ℝ)).partDens.get? i := by
    intro i hi
    simp only [partDens, Stream'.Seq.map_get?]
    interval_cases i
    · rw [head _ (by norm_num [Int.fract]), head _ (by norm_num [Int.fract])]
      norm_num [Int.fract]
    · rw [of_s_succ, of_s_succ]
      rw [head _ (by norm_num [Int.fract]), head _ (by norm_num [Int.fract])]
      norm_num [Int.fract]
  convert abs_sub_le_of_contFrac_prefix_eq _ _ 2 (by norm_num [of_h_eq_floor]) hd using 1
  norm_num

-- Once both expansions have stopped, every later pair of missing digits agrees.
example (x y : ℝ) (k m : ℕ) (h0 : (of x).h = (of y).h)
    (hm : ∀ i < m, (of x).partDens.get? i = (of y).partDens.get? i)
    (hx : (of x).TerminatedAt m) (hy : (of y).TerminatedAt m) :
    |x - y| ≤ 2 ^ (1 - (k : ℤ)) := by
  apply abs_sub_le_of_contFrac_prefix_eq _ _ _ h0
  intro i _
  rcases lt_or_ge i m with hi | hi
  · exact hm i hi
  · rw [terminatedAt_iff_partDen_none.mp (terminated_stable hi hx),
      terminatedAt_iff_partDen_none.mp (terminated_stable hi hy)]
