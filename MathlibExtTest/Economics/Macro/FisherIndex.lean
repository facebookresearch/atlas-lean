/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Macro.FisherIndex
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Macro.FisherIndex` -/

namespace MathlibExtTest.Economics.Macro.FisherIndex

open MathlibExt.Economics.Macro.FisherIndex

/-- Different two-good basket: base prices `(2, 1)`, current prices `(3, 2)`,
base basket `(2, 1)`, current basket `(1, 2)`. -/
example :
    fisherIndex ![3, 2] ![2, 1] ![1, 2] ![2, 1] (Finset.univ : Finset (Fin 2)) *
        fisherIndex ![2, 1] ![3, 2] ![2, 1] ![1, 2] (Finset.univ : Finset (Fin 2)) = 1 := by
  apply fisher_time_reversal <;> simp [Fin.sum_univ_two] <;> norm_num

/-- Laspeyres for the same basket, from the definition:
`(3 * 2 + 2 * 1) / (2 * 2 + 1 * 1) = 8 / 5`. -/
example : laspeyres ![2, 1] ![3, 2] ![2, 1] (Finset.univ : Finset (Fin 2)) = 8 / 5 := by
  unfold laspeyres
  simp [Fin.sum_univ_two]
  norm_num

/-- Paasche for the same basket, from the definition:
`(3 * 1 + 2 * 2) / (2 * 1 + 1 * 2) = 7 / 4`. -/
example : paasche ![2, 1] ![3, 2] ![1, 2] (Finset.univ : Finset (Fin 2)) = 7 / 4 := by
  unfold paasche
  simp [Fin.sum_univ_two]
  norm_num

/-- Exact Fisher value from the definitions, with distinct Laspeyres and Paasche
indices: base prices `(1, 1)`, current prices `(2, 8)`, base basket `(1, 0)`, current
basket `(0, 1)` give Laspeyres `2`, Paasche `8`, and Fisher `√(2 * 8) = 4`. -/
example : fisherIndex ![1, 1] ![2, 8] ![1, 0] ![0, 1] (Finset.univ : Finset (Fin 2)) = 4 := by
  have hL : laspeyres ![1, 1] ![2, 8] ![1, 0] (Finset.univ : Finset (Fin 2)) = 2 := by
    unfold laspeyres
    simp [Fin.sum_univ_two]
  have hP : paasche ![1, 1] ![2, 8] ![0, 1] (Finset.univ : Finset (Fin 2)) = 8 := by
    unfold paasche
    simp [Fin.sum_univ_two]
  unfold fisherIndex
  rw [hL, hP, show (2 : ℝ) * 8 = 4 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

end MathlibExtTest.Economics.Macro.FisherIndex
