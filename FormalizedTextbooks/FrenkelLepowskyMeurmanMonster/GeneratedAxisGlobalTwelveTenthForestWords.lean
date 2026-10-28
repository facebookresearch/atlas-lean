/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestData

/-! A fast list evaluator for the binary action of words in the six gated Tenth letters, and the
finite check that the row operations of every doubling step compute the action of its word on
the 24 basis masks. The letter columns are the gated Tenth projection columns; their
identification is proved where that data is imported. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The binary columns of the six gated Tenth letters, indexed by natural numbers. -/
def tenthForestLetterColsNat : ℕ → List ℕ
  | 0 => [
    7955550, 7915523, 3463389, 1018088, 12128748, 2293325, 11344335, 831064, 262179, 3561498,
    14679902, 3459075, 49164, 4295300, 8837008, 9811878, 16195645, 13628364, 12046386, 15926211,
    10909719, 16552937, 7579701, 7718445]
  | 1 => [
    1459712, 11796389, 4935173, 9811473, 13198897, 6323687, 2598465, 6050631, 3352321, 3917888,
    3235905, 7825462, 960014, 8848470, 15731808, 4637815, 15141473, 9661015, 4661640, 5767798,
    3631680, 1030577, 6025231, 16124276]
  | 2 => [
    7340033, 983042, 4589576, 4786180, 6070314, 7102486, 5464198, 6529098, 4528654, 4856078,
    4183822, 2048, 4096, 8331264, 7768064, 7948288, 131072, 65536, 524288, 262144, 6291456,
    5242880, 4194304, 11583500]
  | 3 => [
    6767468, 4855096, 14842213, 13299311, 4562170, 6456820, 16567164, 5091872, 14778072,
    10977232, 4210354, 4523004, 9858960, 16003528, 4676923, 7330353, 6837588, 1150552, 5231264,
    377518, 4522668, 4852398, 4855820, 15656194]
  | 4 => [
    697856, 14133089, 15430952, 2401801, 16115570, 11829115, 9214811, 2705025, 16301476,
    16132372, 9129180, 108598, 6284856, 9045163, 9071787, 1089, 8489642, 8596124, 7211454,
    139840, 1714752, 1962417, 1568783, 10644276]
  | 5 => [
    7340033, 983042, 4589576, 4786180, 6070314, 7102486, 5464198, 6529098, 4528654, 4856078,
    4183822, 2048, 4096, 8331264, 7768064, 7948288, 131072, 65536, 524288, 262144, 6291456,
    5242880, 4194304, 11583500]
  | _ => []

/-- The binary columns of a gated Tenth letter. -/
def tenthForestLetterCols (g : Fin 6) : List ℕ := tenthForestLetterColsNat g.val

/-- The XOR of the columns selected by the bits of `v`. -/
def tenthForestApplyCols : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, v => (if v % 2 = 1 then c else 0) ^^^ tenthForestApplyCols cs (v / 2)

/-- The binary action of a letter word (the last letter acts first). -/
def tenthForestWordApply (w : List (Fin 6)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => tenthForestApplyCols (tenthForestLetterCols g) m) v

set_option maxRecDepth 100000 in
-- Finite check: every stage word list matches its row-operation list in length.
theorem tenthForestStage_length :
    ∀ s < 5, (tenthForestStageOps s).length = (tenthForestStageWords s).length := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 1: the row operations compute each word on the 24 basis masks.
theorem tenthForestStage_basis_words_0 :
    ∀ p ∈ (tenthForestStageOps 0).zip (tenthForestStageWords 0), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = tenthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 2: the row operations compute each word on the 24 basis masks.
theorem tenthForestStage_basis_words_1 :
    ∀ p ∈ (tenthForestStageOps 1).zip (tenthForestStageWords 1), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = tenthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 3: the row operations compute each word on the 24 basis masks.
theorem tenthForestStage_basis_words_2 :
    ∀ p ∈ (tenthForestStageOps 2).zip (tenthForestStageWords 2), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = tenthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 4: the row operations compute each word on the 24 basis masks.
theorem tenthForestStage_basis_words_3 :
    ∀ p ∈ (tenthForestStageOps 3).zip (tenthForestStageWords 3), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = tenthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 5: the row operations compute each word on the 24 basis masks.
theorem tenthForestStage_basis_words_4 :
    ∀ p ∈ (tenthForestStageOps 4).zip (tenthForestStageWords 4), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = tenthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

/-- The row operations of every step compute its word on the 24 basis masks. -/
theorem tenthForestStage_basis_words (s : ℕ) (hs : s < 5) :
    ∀ p ∈ (tenthForestStageOps s).zip (tenthForestStageWords s), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = tenthForestWordApply p.2 (2 ^ j) := by
  match s, hs with
  | 0, _ => exact tenthForestStage_basis_words_0
  | 1, _ => exact tenthForestStage_basis_words_1
  | 2, _ => exact tenthForestStage_basis_words_2
  | 3, _ => exact tenthForestStage_basis_words_3
  | 4, _ => exact tenthForestStage_basis_words_4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
