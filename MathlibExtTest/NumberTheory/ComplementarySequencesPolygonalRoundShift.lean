/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ComplementarySequencesPolygonalRoundShift

/-!
# Tests for shifted rounding of non-polygonal numbers
-/

open MetaMathlibExt

private def evenGapPolygonal (d j : ℕ) : ℕ := 2 * d * j * (j - 1) / 2 + j

-- Independently count entries around the skipped polygonal values 14 and 16.
example : nthNonValue (evenGapPolygonal 6) 12 = 13 ∧ nthNonValue (evenGapPolygonal 6) 13 = 15 ∧
    nthNonValue (evenGapPolygonal 7) 15 = 17 := by
  have hform (d j : ℕ) : evenGapPolygonal d j = d * j * (j - 1) + j := by
    rw [evenGapPolygonal, show 2 * d * j * (j - 1) = 2 * (d * j * (j - 1)) by ac_rfl]
    omega
  have hgap (d : ℕ) (hd : 1 ≤ d) (j : ℕ) (hj : 1 ≤ j) :
      evenGapPolygonal d j + j ≤ evenGapPolygonal d (j + 1) := by
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [hform, Nat.add_sub_cancel]
    rw [show d * (i + 1 + 1) * (i + 1) = d * (i + 1) * i + 2 * (d * (i + 1)) by ring]
    have hi : i + 1 ≤ d * (i + 1) := by simpa using Nat.mul_le_mul_right (i + 1) hd
    omega
  have h14 := nthNonValue_eq_one_step (evenGapPolygonal 6) (by decide) (hgap 6 (by decide))
  have h16 := nthNonValue_eq_one_step (evenGapPolygonal 7) (by decide) (hgap 7 (by decide))
  exact ⟨(h14 12 (by decide)).trans (by decide), (h14 13 (by decide)).trans (by decide),
    (h16 15 (by decide)).trans (by decide)⟩

-- Independently check a value below the rounding cutoff, an exact tie, and a case where
-- (k - 2) / 4 is not integral and rounding the shift down instead would give the wrong offset.
private theorem shiftedOffsets :
    ⌊Real.sqrt ((2 * 12 - 2 + ((14 + 1) / 4 : ℕ)) / ((14 : ℝ) - 2)) + 1 / 2⌋₊ = 1 ∧
    ⌊Real.sqrt ((2 * 13 - 2 + ((14 + 1) / 4 : ℕ)) / ((14 : ℝ) - 2)) + 1 / 2⌋₊ = 2 ∧
    ⌊Real.sqrt ((2 * 15 - 2 + ((16 + 1) / 4 : ℕ)) / ((16 : ℝ) - 2)) + 1 / 2⌋₊ = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (2 * 12 - 2 + ((14 + 1) / 4 : ℕ)) / ((14 : ℝ) - 2) = 25 / 12 by norm_num]
    have hlo : (1 / 2 : ℝ) ≤ Real.sqrt (25 / 12) :=
      (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    have hhi : Real.sqrt (25 / 12) < (3 / 2 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    apply (Nat.floor_eq_iff (by positivity)).2
    simp only [Nat.cast_one]
    exact ⟨by linarith only [hlo], by linarith only [hhi]⟩
  · rw [show (2 * 13 - 2 + ((14 + 1) / 4 : ℕ)) / ((14 : ℝ) - 2) = (3 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), show (3 / 2 + 1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Nat.floor_natCast]
  · rw [show (2 * 15 - 2 + ((16 + 1) / 4 : ℕ)) / ((16 : ℝ) - 2) = 16 / 7 by norm_num]
    have hlo : (3 / 2 : ℝ) ≤ Real.sqrt (16 / 7) :=
      (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    have hhi : Real.sqrt (16 / 7) < (5 / 2 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    apply (Nat.floor_eq_iff (by positivity)).2
    simp only [Nat.cast_ofNat]
    exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

-- Exercise the public theorem at the same indices, beyond the unshifted range k ≤ 10.
example : nthNonValue (evenGapPolygonal 6) 12 = 13 ∧ nthNonValue (evenGapPolygonal 6) 13 = 15 ∧
    nthNonValue (evenGapPolygonal 7) 15 = 17 := by
  refine ⟨(nthNonValue_polygonal_eq_round_shift 14 (by decide) 12 (by decide)).trans ?_,
    (nthNonValue_polygonal_eq_round_shift 14 (by decide) 13 (by decide)).trans ?_,
    (nthNonValue_polygonal_eq_round_shift 16 (by decide) 15 (by decide)).trans ?_⟩
  · simp only [Nat.cast_ofNat, shiftedOffsets.1]
  · simp only [Nat.cast_ofNat, shiftedOffsets.2.1]
  · simp only [Nat.cast_ofNat, shiftedOffsets.2.2]
