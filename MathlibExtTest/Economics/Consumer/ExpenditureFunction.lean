/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.ExpenditureFunction
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.Economics.Consumer.ExpenditureFunction` (Atlas EC04.T01). -/

namespace MathlibExtTest.Economics.Consumer.ExpenditureFunction

open MathlibExt.Economics.ExpenditureFunction

example (p : Fin 2 → ℝ) :
    expenditure (fun x => x 0 + x 1) {x | 0 ≤ x} ((2 : ℝ) • p) 1 =
      (2 : ℝ) * expenditure (fun x => x 0 + x 1) {x | 0 ≤ x} p 1 :=
  expenditure_smul _ _ _ _ (by norm_num)

example :
    ConcaveOn ℝ {p : Fin 2 → ℝ | ∀ i, 0 < p i}
      (fun p => expenditure (fun x => x 0 + x 1) {x | 0 ≤ x} p 1) := by
  apply concaveOn_expenditure_pos
  · intro x hx i
    exact hx i
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · norm_num

end MathlibExtTest.Economics.Consumer.ExpenditureFunction
