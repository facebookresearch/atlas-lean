/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ComplementarySequencesPolygonalRound

/-!
# Tests for the rounding formula for non-polygonal numbers
-/

open MetaMathlibExt

-- Compute the first, eighth, and ninth non-values directly with the finite counting formula.
-- The positive decagonal numbers start at 1, 10, 27, so the complement skips 10 after 9.
example :
    let f := fun j : ℕ => (10 - 2) * j * (j - 1) / 2 + j
    nthNonValue f 1 = 2 ∧ nthNonValue f 8 = 9 ∧ nthNonValue f 9 = 11 := by
  intro f
  have hf (j : ℕ) : f j = 4 * j * (j - 1) + j := by
    change 8 * j * (j - 1) / 2 + j = _
    rw [show 8 * j * (j - 1) = 2 * (4 * j * (j - 1)) by ring]
    omega
  have hgap (m : ℕ) (hm : 1 ≤ m) : f m + m ≤ f (m + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 1 := ⟨m - 1, by omega⟩
    simp only [hf, Nat.add_sub_cancel]
    ring_nf
    omega
  have hcount := nthNonValue_eq_one_step f (by decide) hgap
  exact ⟨(hcount 1 (by decide)).trans (by decide), (hcount 8 (by decide)).trans (by decide),
    (hcount 9 (by decide)).trans (by decide)⟩

-- Verify the rounded offsets independently at a half-integer tie, at the last index before
-- skipping 10, and at the next index, where the square root is again a half-integer.
private theorem decagonalRoundedOffsets :
    ⌊Real.sqrt (2 * 1 / ((10 : ℝ) - 2)) + 1 / 2⌋₊ = 1 ∧
    ⌊Real.sqrt (2 * 8 / ((10 : ℝ) - 2)) + 1 / 2⌋₊ = 1 ∧
    ⌊Real.sqrt (2 * 9 / ((10 : ℝ) - 2)) + 1 / 2⌋₊ = 2 := by
  have hs₁ : Real.sqrt (2 * 1 / ((10 : ℝ) - 2)) = 1 / 2 := by
    rw [show 2 * 1 / ((10 : ℝ) - 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs₉ : Real.sqrt (2 * 9 / ((10 : ℝ) - 2)) = 3 / 2 := by
    rw [show 2 * 9 / ((10 : ℝ) - 2) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs₁, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Nat.floor_one]
  · rw [show 2 * 8 / ((10 : ℝ) - 2) = 2 by norm_num]
    have hlo : (1 / 2 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    have hhi : Real.sqrt 2 < (3 / 2 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor <;> norm_num <;> linarith
  · rw [hs₉, show (3 / 2 + 1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]

-- A client of the public theorem also obtains the ninth non-decagonal number.
example : nthNonValue (fun j : ℕ => (10 - 2) * j * (j - 1) / 2 + j) 9 = 11 := by
  rw [nthNonValue_polygonal_eq_round 10 (by decide) (by decide) 9 (by decide)]
  change 9 + ⌊Real.sqrt (2 * 9 / ((10 : ℝ) - 2)) + 1 / 2⌋₊ = 11
  rw [decagonalRoundedOffsets.2.2]
