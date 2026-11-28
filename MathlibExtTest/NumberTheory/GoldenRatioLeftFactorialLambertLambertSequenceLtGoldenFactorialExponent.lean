/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertLambertSequenceLtGoldenFactorialExponent
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import MathlibExt.NumberTheory.GoldenRatioLambertSequence

/-!
# Tests for the Lambert sequence bound

We construct lower-branch witnesses at indices eight and thirty-two and apply the
bound by the golden factorial exponent.
-/

namespace MathlibExtTest.NumberTheory
namespace GoldenRatioLeftFactorialLambertLambertSequenceLtGoldenFactorialExponent

open MetaMathlibExt Real

/-
The proof of `exists_witness` is adapted from `MetaMathlibExt.exists_lambertSequence` in
`WantedExt/NumberTheory/GoldenRatioLeftFactorialLambertWanted.lean` of
`facebookresearch/atlas-lean`, revision `23d85f13aa5470466339c40e7dc0a9f142c4737d`.
Copyright (c) Meta Platforms, Inc. and affiliates. Licensed under the repository's
LICENSE (Apache License, Version 2.0). The source file lists no individual authors.
-/
private theorem exists_witness (n : ℕ) (hn : 4 ≤ n) :
    ∃ a : ℝ, (n : ℝ) - 1 ≤ a ∧
      lambertMap (-a / ((n : ℝ) - 1)) =
        -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 1 := by linarith
  have hr0 : 0 < (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) := rpow_pos_of_pos (by norm_num) _
  have hr1 : (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) ≤ 1 :=
    rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have he : (1 / 3 : ℝ) < exp (-1) := by
    rw [exp_neg, one_div]
    exact (inv_lt_inv₀ (by norm_num) (exp_pos _)).mpr exp_one_lt_three
  have hq : 1 / ((n : ℝ) - 1) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hd (by norm_num)]
    linarith
  obtain ⟨⟨y, hy⟩, hyx⟩ := (existsUnique_lambertMap_lower_preimage
    (x := -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)))
    (by nlinarith [one_div_pos.mpr hd]) (by nlinarith [one_div_pos.mpr hd])).exists
  refine ⟨-((n : ℝ) - 1) * y, by nlinarith [show y ≤ -1 from hy], ?_⟩
  rw [show -(-((n : ℝ) - 1) * y) / ((n : ℝ) - 1) = y by field_simp]
  exact hyx

example : ∃ a : ℝ, 7 ≤ a ∧
    lambertMap (-a / 7) = -(1 / 7) * (4 / 7 : ℝ) ^ (1 / 7 : ℝ) ∧ a < 23 := by
  obtain ⟨a, ha, hW⟩ := exists_witness 8 (by norm_num)
  have h := lambertSequence_lt_goldenFactorialExponent 8 (by norm_num) a ha hW
  have hphi : (8 / 5 : ℝ) < goldenRatio := by
    nlinarith [goldenRatio_sq, one_lt_goldenRatio]
  have hm : goldenFactorialExponent 8 ≤ 23 := goldenFactorialExponent_le (by norm_num)
    (calc
      _ ≤ (8 / 5 : ℝ) ^ (23 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hphi.le 23)
  refine ⟨a, ?_, ?_, h.trans_le ?_⟩
  · simpa only [Nat.cast_ofNat, show (8 : ℝ) - 1 = 7 by norm_num] using ha
  · simpa only [Nat.cast_ofNat, show (8 : ℝ) - 1 = 7 by norm_num] using hW
  · exact_mod_cast hm

example : ∃ a : ℝ, 31 ≤ a ∧
    lambertMap (-a / 31) = -(1 / 31) * (4 / 7 : ℝ) ^ (1 / 31 : ℝ) ∧
    a < goldenFactorialExponent 32 := by
  obtain ⟨a, ha, hW⟩ := exists_witness 32 (by norm_num)
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (32 : ℝ) - 1 = 31 by norm_num] using ha
  · simpa only [Nat.cast_ofNat, show (32 : ℝ) - 1 = 31 by norm_num] using hW
  · exact lambertSequence_lt_goldenFactorialExponent 32 (by norm_num) a ha hW

end GoldenRatioLeftFactorialLambertLambertSequenceLtGoldenFactorialExponent
end MathlibExtTest.NumberTheory
