/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HoradamCompositionSumRecurrence
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace MetaMathlibExt

private noncomputable def weightedSum (q d e : ℂ) (m : ℕ) : ℂ :=
  ∑ c : Composition m, d ^ (m - c.length) *
    ∏ i : Fin c.length, ((q + e) * (c.blocksFun i : ℂ) - e)

private lemma weightedSum_one : weightedSum 1 1 2 1 = 1 := by
  have huniv : (Finset.univ : Finset (Composition 1)) = {Composition.ones 1} := by
    ext c
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply (Composition.eq_ones_iff_length (c := c)).2
    have hle := c.length_le
    have hpos := c.length_pos_iff.2 (by decide)
    omega
  norm_num [weightedSum, huniv, Composition.ones_length, Composition.ones_blocksFun]

private lemma weightedSum_two : weightedSum 1 1 2 2 = 5 := by
  let a := Composition.single 2 (by decide)
  let b := Composition.ones 2
  have hab : a ≠ b := by
    intro h
    have hlen := congrArg Composition.length h
    norm_num [a, b, Composition.single_length, Composition.ones_length] at hlen
  have huniv : (Finset.univ : Finset (Composition 2)) = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [composition_card, hab]
  rw [weightedSum, huniv, Finset.sum_insert (by simpa using hab)]
  norm_num [a, b, Composition.single_length, Composition.single_blocksFun,
    Composition.ones_length, Composition.ones_blocksFun]

-- At the first valid index, the sums of degrees one and two give w₃ = 16.
example : weightedSum 1 1 2 3 = 16 := by
  have h := horadam_composition_sum_recurrence 2 1 3 1 (by norm_num) (by norm_num) 3 (by decide)
  have hrec : weightedSum 1 1 2 3 = 3 * weightedSum 1 1 2 2 + weightedSum 1 1 2 1 := by
    norm_num [weightedSum] at h ⊢
    exact h
  rw [hrec, weightedSum_two, weightedSum_one]
  norm_num

-- Negative scaling and a zero weight for singleton blocks.
example : weightedSum 0 (-2) (-3) 5 =
    (-4) * weightedSum 0 (-2) (-3) 4 + 2 * weightedSum 0 (-2) (-3) 3 := by
  have h := horadam_composition_sum_recurrence 3 0 (-4) 2 (by norm_num) (by norm_num) 5 (by decide)
  norm_num [weightedSum] at h ⊢
  exact h

end MetaMathlibExt
