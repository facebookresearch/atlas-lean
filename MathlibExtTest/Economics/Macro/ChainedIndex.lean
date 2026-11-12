/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.ChainedIndex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open MathlibExt.Economics.Macro.ChainedIndex
/-!
# Tests for chained-index non-additivity

The one-link case is additive (chained total `150` = components `50 + 100`),
and a zero base quantity has no quantity ratio, so no component equation is
claimed there.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.ChainedIndex

/-- One-link case is additive: growth 3/4, chained total 150 = components 50 + 100. -/
theorem one_link_growth :
    laspeyresVolumeGrowth ![1, 1] ![100, 100] ![50, 100] = 3 / 4 := by
  unfold laspeyresVolumeGrowth
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- One-link additivity: components 50 + 100 sum to the chained total 150. -/
theorem one_link_additive :
    chainedComponentValue 100 100 50 + chainedComponentValue 100 100 100 =
      chainedRealValue (∑ i, ![1, 1] i * ![100, 100] i)
        (laspeyresVolumeGrowth ![1, 1] ![100, 100] ![50, 100]) := by
  unfold chainedComponentValue chainedRealValue laspeyresVolumeGrowth
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Explicit values: total 150, components 50 and 100. -/
theorem one_link_values :
    chainedRealValue 200 (3 / 4) = 150 ∧
      chainedComponentValue 100 100 50 = 50 ∧
        chainedComponentValue 100 100 100 = 100 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold chainedRealValue
    norm_num
  · unfold chainedComponentValue
    norm_num
  · unfold chainedComponentValue
    norm_num

/-- Degenerate `q₀ = 0` check: a zero base quantity has no quantity ratio, so the
component equation is NOT claimed there. Counterexample: LHS = 0, RHS = 50. -/
theorem degenerate_q0_zero_not_claimed :
    chainedComponentValue (1 * 0) 0 50 ≠ 1 * 50 := by
  unfold chainedComponentValue
  norm_num
end MathlibExtTest.Economics.Macro.ChainedIndex
