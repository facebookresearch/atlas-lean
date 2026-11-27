/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.CountIncrement

namespace MetaMathlibExt.beatty_card_compl_between_succ_sub

open Set Real

-- For α = √2, the lower endpoints start at 1, 2, 4, so both increments occur.
example :
    let α := √2
    let β := conjExponent α
    let r (m : ℤ) : ℤ := (Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard
    r 2 - r 1 = 1 ∧ r 3 - r 2 = 0 := by
  have hlo : 4 / 3 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi := sqrt_two_lt_three_halves
  have ha₁ : beattySeq (√2) 1 = 1 := by
    norm_num [beattySeq, Int.floor_eq_iff]
  have ha₂ : beattySeq (√2) 2 = 2 := by
    norm_num [beattySeq, Int.floor_eq_iff]
    linarith
  have ha₃ : beattySeq (√2) 3 = 4 := by
    norm_num [beattySeq, Int.floor_eq_iff]
    constructor <;> linarith
  have step (n : ℤ) (hn : 0 < n) :=
    beatty_card_compl_between_succ_sub irrational_sqrt_two one_lt_sqrt_two (by linarith)
      (HolderConjugate.conjExponent one_lt_sqrt_two).inv_add_inv_eq_one hn
  obtain ⟨_, iff₁⟩ := step 1 (by decide)
  obtain ⟨cases₂, iff₂⟩ := step 2 (by decide)
  refine ⟨iff₁.mpr (by norm_num [ha₁, ha₂]), cases₂.resolve_right (fun h ↦ ?_)⟩
  have := iff₂.mp h
  norm_num [ha₂, ha₃] at this

end MetaMathlibExt.beatty_card_compl_between_succ_sub
