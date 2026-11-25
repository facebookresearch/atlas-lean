/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.LMSR
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# LMSR market maker tests on `Fin 2` with `b = 1`

Ground-truth checks for `MathlibExt.GameTheory.LMSR`: cost, softmax prices,
and maker loss on two-outcome markets. All proofs are `sorry`-free and use
only proved production lemmas (no sorried theorems).
-/

namespace MathlibExtTest.GameTheory.LMSR

open scoped BigOperators
open MathlibExt.GameTheory.LMSR

/-- T1: cost of the zero portfolio is `log 2`. -/
theorem lmsrCost_one_zero : lmsrCost 1 ![0, 0] = Real.log 2 := by
  simp [lmsrCost, Real.logSumExp, Fin.sum_univ_two]
  norm_num

/-- T2: both zero-portfolio prices are `1 / 2` (outcome `0`). -/
theorem lmsrPrice_one_zero_zero : lmsrPrice 1 ![0, 0] 0 = 1 / 2 := by
  simp [lmsrPrice, Real.softmax, Fin.sum_univ_two]
  norm_num

/-- T2: both zero-portfolio prices are `1 / 2` (outcome `1`). -/
theorem lmsrPrice_one_zero_one : lmsrPrice 1 ![0, 0] 1 = 1 / 2 := by
  simp [lmsrPrice, Real.softmax, Fin.sum_univ_two]
  norm_num

/-- T3: price after buying one share of outcome `0`. -/
theorem lmsrPrice_one_update :
    lmsrPrice 1 ![1, 0] 0 = Real.exp 1 / (Real.exp 1 + 1) := by
  simp [lmsrPrice, Real.softmax, Fin.sum_univ_two]

/-- T4: maker loss on the zero portfolio is `0`. -/
theorem lmsrLoss_one_zero : lmsrLoss 1 ![0, 0] 0 = 0 := by
  simp [lmsrLoss, lmsrCost_one_zero, lmsrCost_zero, Fintype.card_fin]

/-- T5: prices sum to one (via proved `sum_lmsrPrice`). -/
theorem sum_lmsrPrice_one_example :
    ∑ i, lmsrPrice 1 ![2, -1] i = 1 :=
  sum_lmsrPrice 1 ![2, -1]

end MathlibExtTest.GameTheory.LMSR
