/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MaxMinIndecomposabilityLunarHoeffdingExtremalSetNcardLe
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace MathlibExtTest.Combinatorics.Additive
namespace MaxMinIndecomposabilityLunarHoeffdingExtremalSetNcardLe

open MetaMathlibExt

private def fullDigits : Fin 3 → Fin 2 := ![1, 1, 1]

private def twoDigits : Fin 3 → Fin 2 := ![1, 1, 0]

private def unitDigits : Fin 3 → Fin 2 := ![1, 0, 0]

example : fullDigits ∈ lunarHoeffdingExtremalSet 2 2 3 := by
  refine ⟨1, by decide, by decide, Or.inl ?_⟩
  have hc : lunarLevelCount 1 fullDigits = 3 := by decide
  rw [hc]
  norm_num

private lemma twoDigits_mul_unitDigits :
    maxMinMul (digitSeq twoDigits) (digitSeq unitDigits) = digitSeq twoDigits := by
  have hf : ∀ j : ℕ, 2 ≤ j → digitSeq twoDigits j = 0 := by
    intro j hj
    by_cases h : j < 3
    · have he : j = 2 := by omega
      subst j
      decide
    · exact digitSeq_of_le _ (by omega)
  have hu : ∀ j : ℕ, 1 ≤ j → digitSeq unitDigits j = 0 := by
    intro j hj
    by_cases h : j < 3
    · have he : j = 1 ∨ j = 2 := by omega
      rcases he with rfl | rfl <;> decide
    · exact digitSeq_of_le _ (by omega)
  funext k
  rcases k with _ | _ | k
  · decide
  · decide
  · rw [hf (k + 2) (by omega), maxMinMul]
    apply le_antisymm _ (Nat.zero_le _)
    apply Finset.sup_le
    intro p hp
    have hsum := Finset.mem_antidiagonal.mp hp
    by_cases hp0 : p.2 = 0
    · rw [hf p.1 (by omega)]
      simp
    · rw [hu p.2 (by omega)]
      simp

example : twoDigits ∈ lunarHoeffdingExtremalSet 2 2 2 ∧
    ¬ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 - 1 ∧
      (2 : ℝ) / 2 < |(lunarLevelCount i twoDigits : ℝ) - ((2 : ℝ) - i) * 2 / 2| := by
  have hf : lunarLevelCount 1 twoDigits = 2 := by decide
  have hu : lunarLevelCount 1 unitDigits = 1 := by decide
  constructor
  · refine ⟨1, by decide, by decide, Or.inr ⟨twoDigits, unitDigits,
      twoDigits_mul_unitDigits, ?_⟩⟩
    rw [hf, hu]
    norm_num
  · rintro ⟨i, hi, hib, hdev⟩
    have he : i = 1 := by omega
    subst i
    rw [hf] at hdev
    norm_num at hdev

example : ∃ C : ℝ, 0 < C ∧
    ((lunarHoeffdingExtremalSet 2 2 3).ncard : ℝ) ≤ 16 * C * Real.exp (-(9 / 16 : ℝ)) ∧
    ((lunarHoeffdingExtremalSet 2 2 2).ncard : ℝ) ≤ 16 * C * Real.exp (-(1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := lunarHoeffdingExtremalSet_ncard_le (b := 2) (by decide)
  refine ⟨C, hC, ?_, ?_⟩
  · have h := hbound 2 (by decide) 3 (by norm_num)
    convert h using 1; norm_num; ring
  · have h := hbound 2 (by decide) 2 (by norm_num)
    convert h using 1; norm_num; ring

end MaxMinIndecomposabilityLunarHoeffdingExtremalSetNcardLe
end MathlibExtTest.Combinatorics.Additive
