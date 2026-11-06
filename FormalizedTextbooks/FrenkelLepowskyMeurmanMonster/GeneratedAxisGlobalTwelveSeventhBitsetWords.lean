/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhBitsetData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestWords

/-! A list evaluator for the binary action of words in the four Seventh forest letters, and the
finite check that the row operations of every doubling step compute the action of its word on
the 24 basis masks. The letter columns are the gated Seventh letter columns; their
identification is proved where that data is imported. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The binary columns of the four Seventh forest letters, indexed by natural numbers. -/
def seventhBitsetLetterColsNat : ℕ → List ℕ
  | 0 => [
    5512089, 4971979, 1621453, 6349286, 4131407, 1456690, 2008879, 2694205, 3377441, 7169317,
    1594765, 2048, 3309568, 3874816, 4472832, 2719744, 5431296, 5828608, 1609728, 7041024,
    2125824, 2154496, 7102464, 9236480]
  | 1 => [
    2781672, 2569370, 4936860, 299926, 3704076, 5690687, 2007075, 2556142, 7629853, 7008281,
    707932, 2048, 5828608, 8048640, 1093632, 2097152, 6545408, 5074944, 856064, 1740800, 4362240,
    188416, 4612096, 8712192]
  | 2 => [
    1280919, 7458357, 372275, 7305703, 8320484, 7181780, 4964373, 1540224, 603864, 237612,
    503226, 2048, 323584, 4247552, 2600960, 7340032, 5664768, 6414336, 1277952, 6000640, 4427776,
    1077248, 5464064, 12644352]
  | 3 => [
    3539863, 13576413, 14295259, 6098952, 3647510, 9598965, 10737557, 1411206, 1646830, 721022,
    16723791, 4612096, 6144, 1271564, 1802, 3148694, 3115496, 2196368, 2591632, 330360, 918142,
    1933806, 5439494, 13181145]
  | _ => []

/-- The binary columns of a Seventh forest letter. -/
def seventhBitsetLetterCols (g : Fin 4) : List ℕ := seventhBitsetLetterColsNat g.val

/-- The binary action of a letter word (the last letter acts first). -/
def seventhBitsetWordApply (w : List (Fin 4)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => tenthForestApplyCols (seventhBitsetLetterCols g) m) v

set_option maxRecDepth 100000 in
-- Finite check: every stage word list matches its row-operation list in length.
/-- Every stage has as many words as row-operation lists. -/
theorem seventhBitsetStage_length :
    ∀ s < 5, (seventhBitsetStageOps s).length = (seventhBitsetStageWords s).length := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 1: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 1 compute each word on the 24 basis masks. -/
theorem seventhBitsetStage_basis_words_0 :
    ∀ p ∈ (seventhBitsetStageOps 0).zip (seventhBitsetStageWords 0), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = seventhBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 2: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 2 compute each word on the 24 basis masks. -/
theorem seventhBitsetStage_basis_words_1 :
    ∀ p ∈ (seventhBitsetStageOps 1).zip (seventhBitsetStageWords 1), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = seventhBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 3: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 3 compute each word on the 24 basis masks. -/
theorem seventhBitsetStage_basis_words_2 :
    ∀ p ∈ (seventhBitsetStageOps 2).zip (seventhBitsetStageWords 2), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = seventhBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 4: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 4 compute each word on the 24 basis masks. -/
theorem seventhBitsetStage_basis_words_3 :
    ∀ p ∈ (seventhBitsetStageOps 3).zip (seventhBitsetStageWords 3), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = seventhBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 5: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 5 compute each word on the 24 basis masks. -/
theorem seventhBitsetStage_basis_words_4 :
    ∀ p ∈ (seventhBitsetStageOps 4).zip (seventhBitsetStageWords 4), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = seventhBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

/-- The row operations of every step compute its word on the 24 basis masks. -/
theorem seventhBitsetStage_basis_words (s : ℕ) (hs : s < 5) :
    ∀ p ∈ (seventhBitsetStageOps s).zip (seventhBitsetStageWords s), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = seventhBitsetWordApply p.2 (2 ^ j) := by
  match s, hs with
  | 0, _ => exact seventhBitsetStage_basis_words_0
  | 1, _ => exact seventhBitsetStage_basis_words_1
  | 2, _ => exact seventhBitsetStage_basis_words_2
  | 3, _ => exact seventhBitsetStage_basis_words_3
  | 4, _ => exact seventhBitsetStage_basis_words_4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
