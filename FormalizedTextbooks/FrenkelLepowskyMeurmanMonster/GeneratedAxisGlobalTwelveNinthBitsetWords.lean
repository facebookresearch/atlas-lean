/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetData

/-! A fast list evaluator for the binary action of words in the six Ninth letters, and the
finite check that the row operations of every doubling step compute the action of its word on
the 24 basis masks. The letter columns are identified with the actual binary actions where the
letters are defined. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The binary columns of the six Ninth letters, indexed by natural numbers. -/
def ninthForestLetterColsNat : ℕ → List ℕ
  | 0 => [
    780855, 6543924, 4829188, 4813444, 7010241, 2699299, 64, 6543336, 256, 731108, 650091, 2048,
    4397056, 4331520, 2158592, 4718592, 12288, 6959104, 7143424, 2719744, 7929856, 6926336,
    2686976, 12595203]
  | 1 => [
    8864216, 1426514, 3748977, 5546403, 6095172, 8723085, 4311695, 2636831, 5049287, 8982890,
    10672541, 10177181, 13454550, 1971787, 7453440, 16774077, 10739794, 11106214, 6523664,
    6592148, 9926290, 13951737, 13195039, 1359380]
  | 2 => [
    13865918, 14917595, 16361469, 5824116, 549489, 10189828, 7005743, 3867335, 12938000,
    12141665, 7275135, 10660826, 4998022, 846163, 15477023, 4466701, 1305489, 12708297,
    11446991, 788996, 775794, 15494029, 7471959, 10030481]
  | 3 => [
    780855, 6543924, 4829188, 4813444, 7010241, 2699299, 64, 6543336, 256, 731108, 650091, 2048,
    4397056, 4331520, 2158592, 4718592, 12288, 6959104, 7143424, 2719744, 7929856, 6926336,
    2686976, 12595203]
  | 4 => [
    6966702, 576316, 12859193, 4500188, 12023165, 12587354, 1293195, 12141611, 8514318, 4735228,
    1410765, 14817081, 14599690, 3974451, 14617769, 15603210, 13139929, 2146856, 3240467,
    14062505, 7443564, 9834478, 552355, 14551109]
  | 5 => [
    176384, 9912958, 3638067, 8712562, 8026416, 13514064, 5243599, 7326663, 2808848, 15492676,
    5568045, 11696740, 7171710, 13382983, 5166797, 12874348, 13761814, 6672640, 15328610,
    8944241, 9469495, 14546897, 2550016, 9612030]
  | _ => []

/-- The binary columns of a Ninth letter. -/
def ninthForestLetterCols (g : Fin 6) : List ℕ := ninthForestLetterColsNat g.val

/-- The XOR of the columns selected by the bits of `v`. -/
def ninthForestApplyCols : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, v => (if v % 2 = 1 then c else 0) ^^^ ninthForestApplyCols cs (v / 2)

/-- The binary action of a letter word (the last letter acts first). -/
def ninthForestWordApply (w : List (Fin 6)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => ninthForestApplyCols (ninthForestLetterCols g) m) v

set_option maxRecDepth 100000 in
-- Finite check: every stage word list matches its row-operation list in length.
/-- Every stage has as many row-operation lists as words. -/
theorem ninthForestStage_length :
    ∀ s < 5, (ninthForestStageOps s).length = (ninthForestStageWords s).length := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 1: the row operations compute each word on the 24 basis masks.
/-- Stage 1: the row operations compute each word on the 24 basis masks. -/
theorem ninthForestStage_basis_words_0 :
    ∀ p ∈ (ninthForestStageOps 0).zip (ninthForestStageWords 0), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = ninthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 2: the row operations compute each word on the 24 basis masks.
/-- Stage 2: the row operations compute each word on the 24 basis masks. -/
theorem ninthForestStage_basis_words_1 :
    ∀ p ∈ (ninthForestStageOps 1).zip (ninthForestStageWords 1), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = ninthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 3: the row operations compute each word on the 24 basis masks.
/-- Stage 3: the row operations compute each word on the 24 basis masks. -/
theorem ninthForestStage_basis_words_2 :
    ∀ p ∈ (ninthForestStageOps 2).zip (ninthForestStageWords 2), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = ninthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 4: the row operations compute each word on the 24 basis masks.
/-- Stage 4: the row operations compute each word on the 24 basis masks. -/
theorem ninthForestStage_basis_words_3 :
    ∀ p ∈ (ninthForestStageOps 3).zip (ninthForestStageWords 3), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = ninthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 5: the row operations compute each word on the 24 basis masks.
/-- Stage 5: the row operations compute each word on the 24 basis masks. -/
theorem ninthForestStage_basis_words_4 :
    ∀ p ∈ (ninthForestStageOps 4).zip (ninthForestStageWords 4), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = ninthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

/-- The row operations of every step compute its word on the 24 basis masks. -/
theorem ninthForestStage_basis_words (s : ℕ) (hs : s < 5) :
    ∀ p ∈ (ninthForestStageOps s).zip (ninthForestStageWords s), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = ninthForestWordApply p.2 (2 ^ j) := by
  match s, hs with
  | 0, _ => exact ninthForestStage_basis_words_0
  | 1, _ => exact ninthForestStage_basis_words_1
  | 2, _ => exact ninthForestStage_basis_words_2
  | 3, _ => exact ninthForestStage_basis_words_3
  | 4, _ => exact ninthForestStage_basis_words_4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
