/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BeattyDecompositionBeattyCardComplBetweenIsBeatty
import Mathlib.Data.Set.Card

namespace MathlibExtTest.NumberTheory.BeattyDecompositionBeattyCardComplBetweenIsBeatty

open Set Real

-- The count at `n = 1` vanishes: the Beatty value there is `⌊r⌋ = 0`.
example {α β : ℝ} (hirr : Irrational α) (hα1 : 1 < α) (hα2 : α < 2)
    (hαβ : α⁻¹ + β⁻¹ = 1) :
    ((Ioo (beattySeq α 1) (beattySeq β 1) ∩ {beattySeq β k | k > 0}).ncard : ℤ) = 0 := by
  obtain ⟨r, hr0, hr1, hcount⟩ :=
    MetaMathlibExt.beatty_card_compl_between_isBeatty hirr hα1 hα2 hαβ
  have h1 := hcount 1 (by decide)
  rw [h1]
  have key : ⌊r⌋ = 0 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  simpa only [beattySeq, Int.cast_one, one_mul] using key

-- For `α = √2`, the counts form a Beatty sequence.
example :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ n : ℤ, 0 < n →
      ((Ioo (beattySeq √2 n) (beattySeq (conjExponent √2) n) ∩
        {beattySeq (conjExponent √2) k | k > 0}).ncard : ℤ) = beattySeq r n :=
  MetaMathlibExt.beatty_card_compl_between_isBeatty irrational_sqrt_two one_lt_sqrt_two
    (by linarith [sqrt_two_lt_three_halves])
    (HolderConjugate.conjExponent one_lt_sqrt_two).inv_add_inv_eq_one

end MathlibExtTest.NumberTheory.BeattyDecompositionBeattyCardComplBetweenIsBeatty
