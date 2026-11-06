/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthForestData

/-! A fast list evaluator for the binary action of words in the sixteen Eighth letters, and the
finite check that the row operations of every doubling step compute the action of its word on
the 24 basis masks. The letter columns are identified with the actual binary actions where the
letters are defined. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The binary columns of the sixteen Eighth letters, indexed by natural numbers. -/
def eighthForestLetterColsNat : ℕ → List ℕ
  | 0 => [
    1, 4196354, 4196356, 4196360, 131088, 65568, 64, 128, 2097408, 1049088, 58368, 2048, 6144,
    8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8445953]
  | 1 => [
    4196353, 2, 4196356, 4196360, 2752528, 1376288, 2752576, 1376384, 655616, 328192, 54272,
    2048, 4096, 10240, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    8441858]
  | 2 => [
    4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016, 46080,
    2048, 4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    8433668]
  | 3 => [
    4196353, 4196354, 4196356, 8, 3538960, 2949152, 1769536, 3539072, 852224, 721408, 29696,
    2048, 4096, 8192, 16384, 34816, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    8417288]
  | 4 => [
    133121, 2754562, 1968132, 3541000, 16, 61472, 2146368, 3170432, 573696, 827904, 1024, 2048,
    4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8450064]
  | 5 => [
    67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856, 811264, 311808, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152, 4194304, 8450080]
  | 6 => [
    1, 2754562, 3737604, 1771528, 2146320, 3186720, 64, 57472, 180480, 221696, 1024, 2048, 4096,
    8192, 16384, 32768, 65536, 131072, 264192, 524288, 1048576, 2097152, 4194304, 8446016]
  | 7 => [
    1, 1378306, 2557956, 3541000, 3170320, 1097760, 57408, 128, 237824, 115200, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 131072, 262144, 526336, 1048576, 2097152, 4194304, 8446080]
  | 8 => [
    2099201, 655362, 458756, 851976, 573456, 811040, 180288, 237696, 256, 4198912, 2100224,
    2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1050624, 2097152, 4194304,
    12587264]
  | 9 => [
    1050625, 327682, 917508, 720904, 827408, 311328, 221248, 114816, 4198656, 512, 1051648,
    2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2099200, 4194304,
    12587520]
  | 10 => [
    57345, 53250, 45060, 28680, 16, 32, 64, 128, 2097408, 1049088, 1024, 2048, 4096, 8192,
    16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632]
  | 11 => [
    1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    262144, 524288, 1048576, 2097152, 4194304, 8388608]
  | 12 => [
    6224192, 6244493, 2270352, 3755432, 4521517, 1373743, 886073, 6224223, 1223725, 2161039,
    5193817, 2048, 4984832, 6180864, 4325376, 36864, 7843840, 5746688, 724992, 4411392, 2719744,
    1359872, 737280, 10186752]
  | 13 => [
    2824443, 3889200, 7061122, 4150072, 4500976, 5799158, 5190195, 5029187, 1751602, 2146576,
    4796599, 2048, 8331264, 2752512, 3874816, 8364032, 4997120, 1540096, 4722688, 2154496,
    2920448, 196608, 1556480, 12169216]
  | 14 => [
    3447264, 4528478, 3955120, 1090908, 1723525, 3080395, 2497731, 5831113, 4546709, 5581391,
    4429384, 2048, 2379776, 1597440, 2510848, 6799360, 2949120, 3309568, 2150400, 7184384,
    5828608, 659456, 2756608, 15728640]
  | 15 => [
    5011269, 3703170, 1655119, 4755944, 7479448, 4654636, 3567773, 739218, 2742562, 417021,
    7874952, 2048, 4128768, 2498560, 3252224, 6987776, 1105920, 20480, 7254016, 2052096, 585728,
    6291456, 4554752, 11366400]
  | _ => []

/-- The binary columns of an Eighth letter. -/
def eighthForestLetterCols (g : Fin 16) : List ℕ := eighthForestLetterColsNat g.val

/-- The XOR of the columns selected by the bits of `v`. -/
def eighthForestApplyCols : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, v => (if v % 2 = 1 then c else 0) ^^^ eighthForestApplyCols cs (v / 2)

/-- The binary action of a letter word (the last letter acts first). -/
def eighthForestWordApply (w : List (Fin 16)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => eighthForestApplyCols (eighthForestLetterCols g) m) v

set_option maxRecDepth 100000 in
-- Finite check: every stage word list matches its row-operation list in length.
/-- Every stage has as many row-operation lists as words. -/
theorem eighthForestStage_length :
    ∀ s < 5, (eighthForestStageOps s).length = (eighthForestStageWords s).length := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 1: the row operations compute each word on the 24 basis masks.
/-- Stage 1: the row operations compute each word on the 24 basis masks. -/
theorem eighthForestStage_basis_words_0 :
    ∀ p ∈ (eighthForestStageOps 0).zip (eighthForestStageWords 0), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = eighthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 2: the row operations compute each word on the 24 basis masks.
/-- Stage 2: the row operations compute each word on the 24 basis masks. -/
theorem eighthForestStage_basis_words_1 :
    ∀ p ∈ (eighthForestStageOps 1).zip (eighthForestStageWords 1), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = eighthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 3: the row operations compute each word on the 24 basis masks.
/-- Stage 3: the row operations compute each word on the 24 basis masks. -/
theorem eighthForestStage_basis_words_2 :
    ∀ p ∈ (eighthForestStageOps 2).zip (eighthForestStageWords 2), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = eighthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 4: the row operations compute each word on the 24 basis masks.
/-- Stage 4: the row operations compute each word on the 24 basis masks. -/
theorem eighthForestStage_basis_words_3 :
    ∀ p ∈ (eighthForestStageOps 3).zip (eighthForestStageWords 3), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = eighthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 5: the row operations compute each word on the 24 basis masks.
/-- Stage 5: the row operations compute each word on the 24 basis masks. -/
theorem eighthForestStage_basis_words_4 :
    ∀ p ∈ (eighthForestStageOps 4).zip (eighthForestStageWords 4), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = eighthForestWordApply p.2 (2 ^ j) := by
  decide +kernel

/-- The row operations of every step compute its word on the 24 basis masks. -/
theorem eighthForestStage_basis_words (s : ℕ) (hs : s < 5) :
    ∀ p ∈ (eighthForestStageOps s).zip (eighthForestStageWords s), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = eighthForestWordApply p.2 (2 ^ j) := by
  match s, hs with
  | 0, _ => exact eighthForestStage_basis_words_0
  | 1, _ => exact eighthForestStage_basis_words_1
  | 2, _ => exact eighthForestStage_basis_words_2
  | 3, _ => exact eighthForestStage_basis_words_3
  | 4, _ => exact eighthForestStage_basis_words_4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
