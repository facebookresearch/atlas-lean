/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightForestSteps

/-! The finite check that the row operations of every root-eight doubling step compute the
binary action of its word on the 24 basis masks, using the list evaluator of the letter
columns. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
-- Finite check: every stage word list matches its row-operation list in length.
theorem rootEightForestStage_length :
    ∀ s < 5, (rootEightForestStageOps s).length = (rootEightForestStageWords s).length := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 1: the row operations compute each word on the 24 basis masks.
theorem rootEightForestStage_basis_words_0 :
    ∀ p ∈ (rootEightForestStageOps 0).zip (rootEightForestStageWords 0), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = rootEightForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 2: the row operations compute each word on the 24 basis masks.
theorem rootEightForestStage_basis_words_1 :
    ∀ p ∈ (rootEightForestStageOps 1).zip (rootEightForestStageWords 1), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = rootEightForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 3: the row operations compute each word on the 24 basis masks.
theorem rootEightForestStage_basis_words_2 :
    ∀ p ∈ (rootEightForestStageOps 2).zip (rootEightForestStageWords 2), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = rootEightForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 4: the row operations compute each word on the 24 basis masks.
theorem rootEightForestStage_basis_words_3 :
    ∀ p ∈ (rootEightForestStageOps 3).zip (rootEightForestStageWords 3), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = rootEightForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 5: the row operations compute each word on the 24 basis masks.
theorem rootEightForestStage_basis_words_4 :
    ∀ p ∈ (rootEightForestStageOps 4).zip (rootEightForestStageWords 4), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = rootEightForestWordApply p.2 (2 ^ j) := by
  decide +kernel

/-- The row operations of every step compute its word on the 24 basis masks. -/
theorem rootEightForestStage_basis_words (s : ℕ) (hs : s < 5) :
    ∀ p ∈ (rootEightForestStageOps s).zip (rootEightForestStageWords s), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = rootEightForestWordApply p.2 (2 ^ j) := by
  match s, hs with
  | 0, _ => exact rootEightForestStage_basis_words_0
  | 1, _ => exact rootEightForestStage_basis_words_1
  | 2, _ => exact rootEightForestStage_basis_words_2
  | 3, _ => exact rootEightForestStage_basis_words_3
  | 4, _ => exact rootEightForestStage_basis_words_4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
