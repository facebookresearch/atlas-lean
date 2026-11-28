/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.SelfBetweenIncrement

namespace MetaMathlibExt.beatty_card_self_between_succ_sub

open Set Real

-- The β-Beatty endpoints are 2, 4, and 7, so the count first stays constant, then rises by one.
example :
    let β := 1 + √2
    let α := conjExponent β
    let c (m : ℤ) : ℤ :=
      (Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq α k | k > 0}).ncard
    c 2 - c 1 = 0 ∧ c 3 - c 2 = 1 := by
  let β := 1 + √2
  have hlo : 4 / 3 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi := sqrt_two_lt_three_halves
  have hβ : 2 < β := by dsimp [β]; linarith
  have hirr : Irrational β := by
    simpa only [Int.cast_one] using irrational_sqrt_two.intCast_add 1
  have hconj := HolderConjugate.conjExponent (show 1 < β by linarith)
  have hfloor : ⌊β⌋ = 2 := by
    norm_num [β, Int.floor_eq_iff]
    constructor <;> linarith
  have hb₁ : beattySeq β 1 = 2 := by simpa [beattySeq] using hfloor
  have hb₂ : beattySeq β 2 = 4 := by
    norm_num [β, beattySeq, Int.floor_eq_iff]
    constructor <;> linarith
  have hb₃ : beattySeq β 3 = 7 := by
    norm_num [β, beattySeq, Int.floor_eq_iff]
    constructor <;> linarith
  have step (n : ℤ) (hn : 0 < n) :=
    beatty_card_self_between_succ_sub hirr hβ hconj.symm.inv_add_inv_eq_one hn
  obtain ⟨_, iff₁⟩ := step 1 (by decide)
  obtain ⟨cases₂, iff₂⟩ := step 2 (by decide)
  refine ⟨?_, ?_⟩
  · simpa only [hfloor, Int.reduceAdd, Int.reduceSub] using
      iff₁.mpr (by norm_num [hfloor, hb₁, hb₂])
  · have h := cases₂.resolve_left (fun h ↦ by
      have hgap := iff₂.mp h
      norm_num [hfloor, hb₂, hb₃] at hgap)
    simpa only [hfloor, Int.reduceAdd, Int.reduceSub] using h

end MetaMathlibExt.beatty_card_self_between_succ_sub
