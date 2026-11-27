/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.WeightedZeroSumCosets

namespace MetaMathlibExt

private abbrev hasWeightedZeroSum (A : Subgroup ℚˣ) (x y : ℚ) : Prop :=
  ∃ I : Finset (Fin 2), I.Nonempty ∧ ∃ a : Fin 2 → ℚ,
    (∀ i ∈ I, a i ∈ ((↑) : ℚˣ → ℚ) '' A) ∧ ∑ i ∈ I, a i * ![x, y] i = 0

-- With only the weight 1, the two equal positive terms cannot sum to zero.
example : ¬ hasWeightedZeroSum ⊥ 1 1 := by
  apply (pair_no_weightedZeroSum_iff (⊥ : Subgroup ℚˣ) (x := 1) (y := 1)
    (by norm_num) (by norm_num)).2
  intro heq
  have hmem := QuotientGroup.eq.mp heq
  have hunit := Subgroup.mem_bot.mp hmem
  have hval := congrArg (fun z : ℚˣ => (z : ℚ)) hunit
  norm_num at hval

-- The same weights do give a zero sum for a pair of opposites.
example : hasWeightedZeroSum ⊥ 1 (-1) := by
  by_contra h
  apply (pair_no_weightedZeroSum_iff (⊥ : Subgroup ℚˣ) (x := 1) (y := -1)
    (by norm_num) (by norm_num)).1 h
  apply congrArg QuotientGroup.mk
  ext
  norm_num

-- Allowing all unit weights brings distinct positive terms into the same coset.
example : hasWeightedZeroSum ⊤ 2 3 := by
  by_contra h
  exact (pair_no_weightedZeroSum_iff (⊤ : Subgroup ℚˣ) (x := 2) (y := 3)
    (by norm_num) (by norm_num)).1 h (QuotientGroup.eq.mpr (Subgroup.mem_top _))

end MetaMathlibExt
