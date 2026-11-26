/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.SkippingFiberIndicator
import Mathlib.NumberTheory.Real.GoldenRatio

namespace MetaMathlibExt.beatty_skipping_card_eq_add_indicator

open Set Real
open scoped goldenRatio

private theorem zero_not_mem_and_one_mem {r : ℝ} (hlo : 1 < r) (hhi : r < 2) :
    (0 : ℤ) ∉ {beattySeq r j | j > 0} ∧ (1 : ℤ) ∈ {beattySeq r j | j > 0} := by
  constructor
  · rintro ⟨j, hj, hj0⟩
    have hpos : 0 < beattySeq r j := Int.floor_pos.mpr
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hj) hlo.le)
    simp only [hj0, lt_self_iff_false] at hpos
  · refine ⟨1, by decide, ?_⟩
    rw [beattySeq, Int.cast_one, one_mul, Int.floor_eq_iff]
    norm_num
    exact ⟨hlo.le, hhi⟩

-- With no iteration (`k = 1`), the counts attain zero no times and one exactly once.
example :
    let mult (m : ℕ) := {n : ℤ | 0 < n ∧
      (Ioo (beattySeq (√2) n) (beattySeq (√2 + 2) n) ∩ {beattySeq (√2) j | j > 0}).ncard = m}.ncard
    mult 0 = 0 ∧ mult 1 = 1 := by
  have hlo : 1 < √2 := (lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).2 (by norm_num)
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hconj : HolderConjugate (√2) (√2 + 2) := by
    apply (holderConjugate_iff_eq_conjExponent hlo).2
    apply (eq_div_iff (sub_pos.mpr hlo).ne').2
    nlinarith only [hsq]
  have hinv : 1 / (√2 - 1) = √2 + 1 := by
    apply (div_eq_iff (sub_pos.mpr hlo).ne').2
    nlinarith only [hsq]
  have hδ : -1 + 1 / (√2 - 1) = √2 := by rw [hinv]; ring
  have h := beatty_skipping_card_eq_add_indicator (k := 1) irrational_sqrt_two (by decide)
    (by norm_num; exact hlo) (by norm_num; exact hhi) hconj.inv_add_inv_eq_one
  have h0 := h 0
  have h1 := h 1
  obtain ⟨hz, ho⟩ := zero_not_mem_and_one_mem hlo (by linarith)
  simp only [Nat.sub_self, Function.iterate_zero_apply, hδ, zero_add, Nat.cast_zero, Nat.cast_one,
    indicator_of_notMem hz, indicator_of_mem ho, Pi.one_apply] at h0 h1
  exact ⟨h0, h1⟩

-- With one iteration (`k = 2`), the golden-ratio example has multiplicities one and two.
example :
    let mult (m : ℕ) := {n : ℤ | 0 < n ∧
      (Ioo (beattySeq φ n) (beattySeq (φ + 1) n) ∩ {beattySeq φ j | j > 0}).ncard = m}.ncard
    mult 0 = 1 ∧ mult 1 = 2 := by
  have hsqrt_lo : 2 < √5 := (lt_sqrt (by norm_num)).2 (by norm_num)
  have hsqrt_hi : √5 < 7 / 3 := (sqrt_lt' (by norm_num)).2 (by norm_num)
  have hlo : 3 / 2 < φ := by unfold goldenRatio; linarith
  have hhi : φ < 5 / 3 := by unfold goldenRatio; linarith
  have hconj : HolderConjugate φ (φ + 1) := by
    apply (holderConjugate_iff_eq_conjExponent one_lt_goldenRatio).2
    apply (eq_div_iff (sub_pos.mpr one_lt_goldenRatio).ne').2
    nlinarith only [goldenRatio_sq]
  have hinv : 1 / (φ - 1) = φ := by
    apply (div_eq_iff (sub_pos.mpr one_lt_goldenRatio).ne').2
    nlinarith only [goldenRatio_sq]
  have hinv' : 1 / (2 - φ) = φ + 1 := by
    apply (div_eq_iff (sub_pos.mpr goldenRatio_lt_two).ne').2
    nlinarith only [goldenRatio_sq]
  have hδ : -1 + 1 / (2 - 1 / (φ - 1)) = φ := by rw [hinv, hinv']; ring
  have h := beatty_skipping_card_eq_add_indicator (k := 2) goldenRatio_irrational (by decide)
    (by norm_num; exact hlo) (by norm_num; exact hhi) hconj.inv_add_inv_eq_one
  have h0 := h 0
  have h1 := h 1
  obtain ⟨hz, ho⟩ := zero_not_mem_and_one_mem one_lt_goldenRatio goldenRatio_lt_two
  simp only [show (2 : ℕ) - 1 = 1 by decide, Function.iterate_one, hδ, Nat.cast_zero, Nat.cast_one,
    indicator_of_notMem hz, indicator_of_mem ho, Pi.one_apply, add_zero] at h0 h1
  exact ⟨h0, h1⟩

end MetaMathlibExt.beatty_skipping_card_eq_add_indicator
