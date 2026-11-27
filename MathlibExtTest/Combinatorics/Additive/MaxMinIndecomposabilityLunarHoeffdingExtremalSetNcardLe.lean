/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MaxMinIndecomposabilityLunarHoeffdingExtremalSetNcardLe
import Mathlib.Tactic.NormNum

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

-- Level zero counts representation positions, including trailing zero digits.
example : digitSeq (0 : Fin 1 → Fin 2) = digitSeq (0 : Fin 2 → Fin 2) ∧
    lunarLevelCount 0 (0 : Fin 1 → Fin 2) = 1 ∧
    lunarLevelCount 0 (0 : Fin 2 → Fin 2) = 2 := by
  constructor
  · funext k
    simp [digitSeq]
  · constructor <;> decide

-- Levels at and above the base contain no digits.
example : lunarLevelCount 2 fullDigits = 0 ∧ lunarLevelCount 3 fullDigits = 0 := by
  constructor <;> decide

private lemma zero_product_factor (f g : Fin 3 → Fin 2)
    (hprod : maxMinMul (digitSeq f) (digitSeq g) = digitSeq (0 : Fin 3 → Fin 2)) :
    f = 0 ∨ g = 0 := by
  classical
  by_cases hf : f = 0
  · exact Or.inl hf
  · right
    obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
      by_contra h
      apply hf
      funext a
      simpa using (not_exists.mp h a)
    funext k
    apply Fin.ext
    by_contra hg
    have hfa : 0 < digitSeq f a.val := by
      simpa [digitSeq, a.isLt] using
        (Nat.pos_of_ne_zero (show (f a : ℕ) ≠ 0 by simpa using ha))
    have hgk : 0 < digitSeq g k.val := by
      simpa [digitSeq, k.isLt] using Nat.pos_of_ne_zero hg
    have hpair : (a.val, k.val) ∈ Finset.antidiagonal (a.val + k.val) :=
      Finset.mem_antidiagonal.mpr rfl
    have hle : min (digitSeq f a.val) (digitSeq g k.val) ≤
        maxMinMul (digitSeq f) (digitSeq g) (a.val + k.val) :=
      Finset.le_sup (f := fun p : ℕ × ℕ => min (digitSeq f p.1) (digitSeq g p.2)) hpair
    have hpos := (lt_min hfa hgk).trans_le hle
    rw [hprod] at hpos
    simp [digitSeq] at hpos

-- With both factors restricted to three digits, zero is not extremal here.
example : (0 : Fin 3 → Fin 2) ∉ lunarHoeffdingExtremalSet 2 2 4 := by
  rintro ⟨i, hi, hib, hdev⟩
  have he : i = 1 := by omega
  subst i
  have hz : lunarLevelCount 1 (0 : Fin 3 → Fin 2) = 0 := by decide
  rcases hdev with hdirect | ⟨f, g, hprod, hdev⟩
  · norm_num [hz] at hdirect
  · have count_bound (a : Fin 3 → Fin 2) :
        |(lunarLevelCount 1 a : ℝ) - 3 / 2| ≤ 3 / 2 := by
      have hcount : lunarLevelCount 1 a ≤ 3 := by
        simpa [lunarLevelCount] using
          Finset.card_filter_le (Finset.univ : Finset (Fin 3)) (fun k => 1 ≤ (a k : ℕ))
      have hupper : (lunarLevelCount 1 a : ℝ) ≤ 3 := by exact_mod_cast hcount
      have hlower : 0 ≤ (lunarLevelCount 1 a : ℝ) := Nat.cast_nonneg _
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rcases zero_product_factor f g hprod with rfl | rfl
    · norm_num [hz] at hdev
      linarith [count_bound g]
    · norm_num [hz] at hdev
      linarith [count_bound f]

private def fourDigits : Fin 4 → Fin 2 := ![1, 1, 1, 1]

-- A degree-three factor gives a zero product outside the bounded-factor convention.
example : maxMinMul (digitSeq (0 : Fin 1 → Fin 2)) (digitSeq fourDigits) =
      digitSeq (0 : Fin 3 → Fin 2) ∧
    (4 : ℝ) / 2 <
      |((lunarLevelCount 1 (0 : Fin 1 → Fin 2) + lunarLevelCount 1 fourDigits : ℕ) : ℝ) -
        ((2 : ℝ) - 1) * (2 + 1) / 2| := by
  constructor
  · funext k
    simp [maxMinMul, digitSeq]
  · have hz : lunarLevelCount 1 (0 : Fin 1 → Fin 2) = 0 := by decide
    have hfour : lunarLevelCount 1 fourDigits = 4 := by decide
    norm_num [hz, hfour]

end MaxMinIndecomposabilityLunarHoeffdingExtremalSetNcardLe
end MathlibExtTest.Combinatorics.Additive
