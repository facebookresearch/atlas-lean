/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.ComplBetween
import Mathlib.NumberTheory.Real.GoldenRatio

namespace MetaMathlibExt.beatty_card_compl_between_eq_floor

open Set Real
open scoped goldenRatio

-- The open intervals (1, 2), (3, 5), and (4, 7) contain no β-terms, no β-terms,
-- and just the β-term 5, respectively, for β = φ + 1.
example :
    let count (n : ℤ) : ℤ := (Ioo (beattySeq φ n) (beattySeq (φ + 1) n) ∩
      {beattySeq (φ + 1) k | k > 0}).ncard
    count 1 = 0 ∧ count 2 = 0 ∧ count 3 = 1 := by
  have hconj : HolderConjugate φ (φ + 1) := by
    apply (holderConjugate_iff_eq_conjExponent one_lt_goldenRatio).mpr
    apply (eq_div_iff (sub_ne_zero.mpr one_lt_goldenRatio.ne')).mpr
    nlinarith only [goldenRatio_sq]
  have count {n : ℤ} (hn : 0 < n) :=
    beatty_card_compl_between_eq_floor goldenRatio_irrational one_lt_goldenRatio
      goldenRatio_lt_two hconj.inv_add_inv_eq_one hn
  have hlo : 2 < √5 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : √5 < 7 / 3 := (sqrt_lt (by norm_num : 0 ≤ (5 : ℝ)) (by norm_num)).mpr (by norm_num)
  have hφlo : 3 / 2 < φ := by unfold goldenRatio; linarith
  have hφhi : φ < 5 / 3 := by unfold goldenRatio; linarith
  dsimp only
  rw [count (n := 1) (by decide), count (n := 2) (by decide), count (n := 3) (by decide)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [beattySeq, Int.floor_eq_iff] <;> norm_num <;>
    constructor <;> linarith only [one_lt_goldenRatio, goldenRatio_lt_two, hφlo, hφhi]

end MetaMathlibExt.beatty_card_compl_between_eq_floor
