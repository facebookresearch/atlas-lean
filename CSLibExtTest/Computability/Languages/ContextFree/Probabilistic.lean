/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Probabilistic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for the probabilistic inside recurrence and Chi-Geman bound
-/

open Cslib.Language

namespace CSLibExtTest.Computability.Languages.ContextFree.Probabilistic

/-- `S 2 = q`. -/
theorem test_chiGemanS_two :
    chiGemanS (2 / 3) (1 / 3) 2 = 1 / 3 :=
  chiGemanS_two

/-- `S 3 = 11 / 27`. -/
theorem test_chiGemanS_three :
    chiGemanS (2 / 3) (1 / 3) 3 = 11 / 27 :=
  chiGemanS_three

/-- The main bound at depth five. -/
theorem test_chiGeman_main_five :
    chiGemanS (2 / 3) (1 / 3) 5 ≤ 1 / 2 :=
  chiGeman_main_half 5

/-- Uncaptured mass at cutoff five. -/
theorem test_chiGeman_missing_five :
    1 / 2 ≤ 1 - chiGemanS (2 / 3) (1 / 3) 5 :=
  chiGeman_missing_mass 5

/-- The one-step tree total is `q`. -/
theorem test_cgTotal_one :
    cgTotal (2 / 3) (1 / 3) 1 = 1 / 3 := by
  rw [← chiGemanS_link]
  exact chiGemanS_two

/-- Monotonicity at a step. -/
theorem test_chiGeman_mono_three :
    chiGemanS (2 / 3) (1 / 3) 3 ≤ chiGemanS (2 / 3) (1 / 3) 4 :=
  chiGemanS_mono _ _ (by norm_num) (by norm_num) 3

/-- Upper bound at `p = 1 / 2`. -/
theorem test_chiGemanS_half_le_one_ten :
    chiGemanS (1 / 2) (1 / 2) 10 ≤ 1 :=
  chiGemanS_half_le_one 10

/-- Upper bound at `p = 1 / 3`. -/
theorem test_chiGemanS_third_le_one_ten :
    chiGemanS (1 / 3) (2 / 3) 10 ≤ 1 :=
  chiGemanS_third_le_one 10

/-- Tightness at `p = 1 / 2`: the cutoff sums eventually exceed `9 / 10`,
unlike the `p = 2 / 3` sums, which stay at most `1 / 2`. -/
theorem test_chiGemanS_half_eventually :
    ∀ᶠ h in Filter.atTop, 9 / 10 < chiGemanS (1 / 2) (1 / 2) h :=
  tendsto_chiGemanS_half.eventually (lt_mem_nhds (by norm_num))

/-- Tightness at `p = 1 / 3`: the cutoff sums eventually exceed `9 / 10`. -/
theorem test_chiGemanS_third_eventually :
    ∀ᶠ h in Filter.atTop, 9 / 10 < chiGemanS (1 / 3) (2 / 3) h :=
  tendsto_chiGemanS_third.eventually (lt_mem_nhds (by norm_num))

/-- The Chi-Geman weights are normalized on the example grammar. -/
theorem test_cgWeightFun_normalized :
    IsNormalized Unit ambG cgWeightFun :=
  cgWeightFun_normalized

/-- The violated weights sum to two. -/
theorem test_badWeight_sum :
    ∑ r ∈ ambG.rules.filter (fun r => r.input = ambG.initial),
      badWeightFun r = 2 :=
  badWeight_sum

/-- The violated weights are not a probability. -/
theorem test_badWeight_not_normalized :
    ¬ IsNormalized Unit ambG badWeightFun :=
  badWeight_not_normalized

/-- The two trees are distinct. -/
theorem test_ambT_ne : ambT₁ ≠ ambT₂ :=
  ambT_ne

/-- Both trees yield the ambiguous word. -/
theorem test_ambT_yield : ambT₁.yieldOf = [(), (), ()] ∧
    ambT₂.yieldOf = [(), (), ()] :=
  ambT_yield

/-- Both trees are valid at depth three. -/
theorem test_ambT_mem :
    ambT₁ ∈ treesUpTo Unit ambG 3 ambG.initial [(), (), ()] ∧
      ambT₂ ∈ treesUpTo Unit ambG 3 ambG.initial [(), (), ()] :=
  ambT_mem 3 le_rfl

/-- Exactly two trees derive the ambiguous word at depth three. -/
theorem test_ambT_card :
    (treesUpTo Unit ambG 3 ambG.initial [(), (), ()]).card = 2 := by
  decide

/-- The inside value on the ambiguous word counts both trees. -/
theorem test_inside_three :
    inside Unit ambG cgWeightFun 3 ambG.initial [(), (), ()] =
      2 * ((2 / 3) ^ 2 * (1 / 3) ^ 3) := by
  have hSet : treesUpTo Unit ambG 3 ambG.initial [(), (), ()] =
      {ambT₁, ambT₂} := by
    decide
  rw [inside_eq_treeSum, treeSum, hSet]
  have hne : ambT₁ ∉ ({ambT₂} : Finset (PDerivTree ambG.NT Unit)) := by
    simp only [Finset.mem_singleton, ambT_ne, not_false_eq_true]
  rw [Finset.sum_insert hne, Finset.sum_singleton]
  simp only [ambT₁, ambT₂, PDerivTree.weightOf, cgWeightFun]
  norm_num

/-- The two-tree lower bound on the inside value. -/
theorem test_amb_two_trees_le :
    ambT₁.weightOf cgWeightFun + ambT₂.weightOf cgWeightFun ≤
      inside Unit ambG cgWeightFun 3 ambG.initial [(), (), ()] :=
  amb_two_trees_le cgWeightFun cgWeightFun_normalized.1

/-- Depth five sums the same valid trees as depth three for the three-letter
word. -/
theorem test_inside_stable :
    inside Unit ambG cgWeightFun 5 ambG.initial [(), (), ()] =
      inside Unit ambG cgWeightFun 3 ambG.initial [(), (), ()] :=
  inside_stable Unit ambG cgWeightFun 5 ambG.initial [(), (), ()]
    (by decide)

/-- Positive inside weight lands in the CYK cell. -/
theorem test_cyk_mem :
    ambG.initial ∈
      cykCell ambG ([(), (), ()].length) [(), (), ()] := by
  have hpos : 0 <
      inside Unit ambG cgWeightFun 3 ambG.initial [(), (), ()] := by
    rw [test_inside_three]
    norm_num
  exact mem_cykCell_of_inside_pos Unit ambG ambG_cnf cgWeightFun 3
    ambG.initial [(), (), ()] (by decide) hpos

/-- The right-associated tree is a valid grammar tree of depth at most three. -/
theorem test_mem_ambTreesUpTo : ambT₁ ∈ ambTreesUpTo 3 :=
  (mem_ambTreesUpTo_iff 3 ambT₁).2 ⟨isValidTree_ambG ambT₁, by decide⟩

/-- The grammar's trees of depth at most two weigh `S 3 = 11 / 27`. -/
theorem test_sum_ambTreesUpTo_two :
    ∑ t ∈ ambTreesUpTo 2, t.weightOf cgWeightFun = 11 / 27 := by
  rw [sum_ambTreesUpTo_weightOf cgWeightFun (2 / 3) (1 / 3) rfl rfl 2]
  exact chiGemanS_three

/-- The Chi-Geman bound for the grammar's trees of depth at most five. -/
theorem test_sum_ambTreesUpTo_five_le_half :
    ∑ t ∈ ambTreesUpTo 5, t.weightOf cgWeightFun ≤ 1 / 2 :=
  sum_ambTreesUpTo_cgWeightFun_le_half 5

end CSLibExtTest.Computability.Languages.ContextFree.Probabilistic
