/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatOctA

/-! # The octad terms of the cheap Twelfth source vector are the literal table

The octad Fourier blocks of the cheap Twelfth source vector are evaluated in separate kernel checks
(consecutive ranges of `70` octads of the octad list), each compared with the corresponding range of
the literal octad table. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Flat terms of concatenated octad blocks. -/
theorem twOctsFlat_append :
    ∀ A B : List (ℕ × List (ℕ × ℤ)), octsFlat (A ++ B) = octsFlat A ++ octsFlat B
  | [], B => rfl
  | b :: A, B => by
    simp only [List.cons_append, octsFlat]
    rw [twOctsFlat_append A B, List.append_assoc]

/-- The octad blocks of a concatenated label list. -/
theorem twTriOct_append (K : ℤ) (B : List (ℕ × List (ℕ × ℤ))) (l1 l2 : List ℕ) :
    twTriOct K B (l1 ++ l2) = twTriOct K B l1 ++ twTriOct K B l2 := List.map_append

/-- A suffix splits into a segment and the next suffix. -/
theorem twDropSplit {α : Type} (l : List α) (s n t : ℕ) (h : s + n = t) :
    l.drop s = (l.drop s).take n ++ l.drop t := by
  rw [← h, ← List.drop_drop, List.take_append_drop]

set_option maxRecDepth 100000 in
/-- Octads `280` to `349` of the octad list. -/
theorem twelfthOct_check4 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 280).take 70)))
      ((twelfthOctLit.drop 10560).take 3168) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Octads `350` to `419` of the octad list. -/
theorem twelfthOct_check5 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 350).take 70)))
      ((twelfthOctLit.drop 13728).take 3136) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Octads `420` to `489` of the octad list. -/
theorem twelfthOct_check6 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 420).take 70)))
      ((twelfthOctLit.drop 16864).take 2528) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Octads `490` to `558` of the octad list. -/
theorem twelfthOct_check7 :
    twLBEq (octsFlat (twTriOct 1 twelfthYC.sh.oct ((twelfthSrcOcts.drop 490).take 69)))
      ((twelfthOctLit.drop 19392).take 2688) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The lengths of the octad list and of the literal octad table. -/
theorem twelfthOct_lengths : twelfthSrcOcts.length = 559 ∧ twelfthOctLit.length = 22080 := by
  decide +kernel

/-- The computed octad terms are the literal table. -/
theorem twelfthOct_eq : octsFlat (twTriOct 1 twelfthYC.sh.oct twelfthSrcOcts) = twelfthOctLit := by
  obtain ⟨h1, h2⟩ := twelfthOct_lengths
  have e1 : twelfthSrcOcts.drop 559 = [] := List.drop_eq_nil_of_le (by rw [h1])
  have e2 : twelfthOctLit.drop 22080 = [] := List.drop_eq_nil_of_le (by rw [h2])
  have hs : twelfthSrcOcts = twelfthSrcOcts.drop 0 := rfl
  have hl : twelfthOctLit = twelfthOctLit.drop 0 := rfl
  conv_lhs => rw [hs]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 0 70 70 rfl]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 70 70 140 rfl]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 140 70 210 rfl]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 210 70 280 rfl]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 280 70 350 rfl]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 350 70 420 rfl]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 420 70 490 rfl]
  conv_lhs => rw [twDropSplit twelfthSrcOcts 490 69 559 rfl]
  conv_rhs => rw [hl]
  conv_rhs => rw [twDropSplit twelfthOctLit 0 2176 2176 rfl]
  conv_rhs => rw [twDropSplit twelfthOctLit 2176 2816 4992 rfl]
  conv_rhs => rw [twDropSplit twelfthOctLit 4992 2688 7680 rfl]
  conv_rhs => rw [twDropSplit twelfthOctLit 7680 2880 10560 rfl]
  conv_rhs => rw [twDropSplit twelfthOctLit 10560 3168 13728 rfl]
  conv_rhs => rw [twDropSplit twelfthOctLit 13728 3136 16864 rfl]
  conv_rhs => rw [twDropSplit twelfthOctLit 16864 2528 19392 rfl]
  conv_rhs => rw [twDropSplit twelfthOctLit 19392 2688 22080 rfl]
  rw [e1, e2]
  simp only [twTriOct_append, twOctsFlat_append, List.append_nil]
  rw [twLBEq_eq _ _ twelfthOct_check0, twLBEq_eq _ _ twelfthOct_check1, twLBEq_eq _ _ twelfthOct_check2, twLBEq_eq _ _ twelfthOct_check3, twLBEq_eq _ _ twelfthOct_check4, twLBEq_eq _ _ twelfthOct_check5, twLBEq_eq _ _ twelfthOct_check6, twLBEq_eq _ _ twelfthOct_check7]

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
