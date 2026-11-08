/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Selection.HireAssistantExpected
import all CSLibExt.Algorithms.Lean.Selection.HireAssistant

/-!
# Tests for the expected number of hires

Concrete expected hire counts for `hireAssistant` on uniformly random
orderings of `[1]`, `[1, 2]` and `[1, 2, 3]`, obtained from the harmonic
formula, plus a direct enumeration of all six orderings of `[1, 2, 3]`
by `decide`, independent of the general proof.
-/

open Cslib.Algorithms.Lean.TimeM
open scoped ENNReal

/-- `hireAssistant` on a random ordering of `[1]` makes `1` hire in
expectation (`H_1 = 1`). -/
example : ((uniformPermutation ([1] : List ℕ)).expectENN
    (fun ys => ((hireAssistant ys).time.2 : ℝ≥0∞))).toReal = 1 := by
  rw [hireAssistant_expectedHires_toReal _ (by decide)]
  have hfin : (∑ i : Fin ([1] : List ℕ).length, (1 : ℝ) / (i.val + 1)) =
      ∑ k ∈ Finset.range ([1] : List ℕ).length, (1 : ℝ) / (k + 1) :=
    Fin.sum_univ_eq_sum_range (fun k => (1 : ℝ) / (k + 1)) _
  rw [hfin]
  norm_num [Finset.sum_range_succ]

/-- `hireAssistant` on a random ordering of `[1, 2]` makes `3 / 2` hires
in expectation (`H_2 = 3 / 2`). -/
example : ((uniformPermutation ([1, 2] : List ℕ)).expectENN
    (fun ys => ((hireAssistant ys).time.2 : ℝ≥0∞))).toReal = 3 / 2 := by
  rw [hireAssistant_expectedHires_toReal _ (by decide)]
  have hfin : (∑ i : Fin ([1, 2] : List ℕ).length,
        (1 : ℝ) / (i.val + 1)) =
      ∑ k ∈ Finset.range ([1, 2] : List ℕ).length, (1 : ℝ) / (k + 1) :=
    Fin.sum_univ_eq_sum_range (fun k => (1 : ℝ) / (k + 1)) _
  rw [hfin]
  norm_num [Finset.sum_range_succ]

/-- `hireAssistant` on a random ordering of `[1, 2, 3]` makes `11 / 6`
hires in expectation (`H_3 = 11 / 6`). -/
example : ((uniformPermutation ([1, 2, 3] : List ℕ)).expectENN
    (fun ys => ((hireAssistant ys).time.2 : ℝ≥0∞))).toReal = 11 / 6 := by
  rw [hireAssistant_expectedHires_toReal _ (by decide)]
  have hfin : (∑ i : Fin ([1, 2, 3] : List ℕ).length,
        (1 : ℝ) / (i.val + 1)) =
      ∑ k ∈ Finset.range ([1, 2, 3] : List ℕ).length,
        (1 : ℝ) / (k + 1) :=
    Fin.sum_univ_eq_sum_range (fun k => (1 : ℝ) / (k + 1)) _
  rw [hfin]
  norm_num [Finset.sum_range_succ]

/-- Direct enumeration, independent of the harmonic formula: over the six
orderings of `[1, 2, 3]`, the hire counts total `11`, and `11 / 6` is the
expected number of hires. -/
example : (∑ σ : Equiv.Perm (Fin 3),
    (hireAssistant
      (List.ofFn (fun p => ([1, 2, 3] : List ℕ).get (σ p)))).time.2) =
    11 := by
  decide

#print axioms Cslib.Algorithms.Lean.TimeM.hireAssistant_expectedHires
#print axioms Cslib.Algorithms.Lean.TimeM.hireAssistant_expectedHires_toReal
