/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthBitsetData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestWords

/-! A list evaluator for the binary action of words in the fifteen Sixth generators, and the
finite check that the row operations of every doubling step compute the action of its word on
the 24 basis masks. The letter columns are the gated Sixth generator columns; their
identification is proved where that data is imported. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The binary columns of the fifteen Sixth generators, indexed by natural numbers. -/
def sixthBitsetLetterColsNat : ℕ → List ℕ
  | 0 => [
    1, 4196354, 4196356, 4196360, 131088, 65568, 64, 128, 2097408, 1049088, 58368, 2048, 6144, 8192,
    16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8445953]
  | 1 => [
    4196353, 2, 4196356, 4196360, 2752528, 1376288, 2752576, 1376384, 655616, 328192, 54272, 2048,
    4096, 10240, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8441858]
  | 2 => [
    4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016, 46080, 2048,
    4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8433668]
  | 3 => [
    4196353, 4196354, 4196356, 8, 3538960, 2949152, 1769536, 3539072, 852224, 721408, 29696, 2048,
    4096, 8192, 16384, 34816, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8417288]
  | 4 => [
    67585, 4130818, 4, 3541000, 2109456, 3186720, 3186752, 1056896, 960768, 502272, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 133120, 264192, 524288, 1048576, 2097152, 4194304, 11579488]
  | 5 => [
    198657, 2754562, 4, 2951176, 3182608, 1060896, 1081408, 2138240, 459008, 633344, 1024, 2048,
    4096, 8192, 16384, 32768, 67584, 133120, 262144, 526336, 1048576, 2097152, 4194304, 10530992]
  | 6 => [
    2293761, 3473410, 2099204, 1441800, 536592, 823328, 1222720, 2293888, 303360, 4747776, 2100224,
    2048, 4096, 8192, 16384, 32768, 67584, 133120, 262144, 524288, 1050624, 2097152, 4194304,
    12861744]
  | 7 => [
    1179649, 3080194, 1050628, 3997704, 827408, 274464, 2336832, 3254400, 4772096, 827904, 1051648,
    2048, 4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2099200, 4194304,
    13386256]
  | 8 => [
    124929, 1431554, 3782660, 2979848, 61456, 32, 3186752, 1097856, 2908416, 1360384, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152, 4196352, 8451104]
  | 9 => [
    1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    262144, 524288, 1048576, 2097152, 4194304, 8388608]
  | 10 => [
    2055, 2061, 2059, 2062, 16, 32, 524848, 262928, 2097376, 1048688, 3087, 2048, 4222976, 4247552,
    4239360, 4251648, 2949120, 3538944, 3145728, 1048576, 524288, 786432, 4194304, 12644352]
  | 11 => [
    5100360, 1714560, 8339412, 4014033, 3239040, 7006769, 4534307, 5367311, 3221473, 2238193,
    1438348, 2048, 2125824, 6877184, 2142208, 5877760, 4182016, 323584, 5996544, 6004736, 2195456,
    8187904, 8081408, 11194368]
  | 12 => [
    4306173, 6677282, 3994870, 7434555, 7020743, 2290311, 8221440, 6318056, 2909688, 2649840,
    7453797, 2048, 3612672, 4009984, 8347648, 8335360, 4456448, 7946240, 1740800, 4943872, 253952,
    3510272, 7684096, 12636160]
  | 13 => [
    7402647, 77452, 1705995, 6225855, 3745426, 1948196, 3302166, 5326500, 296569, 6416127, 432006,
    2048, 6987776, 6959104, 3432448, 5951488, 188416, 4009984, 3641344, 6414336, 4718592, 4980736,
    8208384, 12169216]
  | 14 => [
    239617, 525097, 8487838, 1024803, 10714869, 4107008, 3611488, 1239473, 15244485, 16360677,
    15094970, 7421952, 2071630, 3946341, 3489803, 3970917, 1547040, 3199514, 3211275, 526336,
    2284058, 280890, 7667723, 12878737]
  | _ => []

/-- The binary columns of a Sixth generator. -/
def sixthBitsetLetterCols (g : Fin 15) : List ℕ := sixthBitsetLetterColsNat g.val

/-- The binary action of a generator word (the last letter acts first). -/
def sixthBitsetWordApply (w : List (Fin 15)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => tenthForestApplyCols (sixthBitsetLetterCols g) m) v

set_option maxRecDepth 100000 in
-- Finite check: every stage word list matches its row-operation list in length.
/-- Every stage has as many words as row-operation lists. -/
theorem sixthBitsetStage_length :
    ∀ s < 5, (sixthBitsetStageOps s).length = (sixthBitsetStageWords s).length := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 1: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 1 compute each word on the 24 basis masks. -/
theorem sixthBitsetStage_basis_words_0 :
    ∀ p ∈ (sixthBitsetStageOps 0).zip (sixthBitsetStageWords 0), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = sixthBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 2: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 2 compute each word on the 24 basis masks. -/
theorem sixthBitsetStage_basis_words_1 :
    ∀ p ∈ (sixthBitsetStageOps 1).zip (sixthBitsetStageWords 1), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = sixthBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 3: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 3 compute each word on the 24 basis masks. -/
theorem sixthBitsetStage_basis_words_2 :
    ∀ p ∈ (sixthBitsetStageOps 2).zip (sixthBitsetStageWords 2), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = sixthBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 4: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 4 compute each word on the 24 basis masks. -/
theorem sixthBitsetStage_basis_words_3 :
    ∀ p ∈ (sixthBitsetStageOps 3).zip (sixthBitsetStageWords 3), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = sixthBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Finite check for stage 5: the row operations compute each word on the 24 basis masks.
/-- The row operations of stage 5 compute each word on the 24 basis masks. -/
theorem sixthBitsetStage_basis_words_4 :
    ∀ p ∈ (sixthBitsetStageOps 4).zip (sixthBitsetStageWords 4), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = sixthBitsetWordApply p.2 (2 ^ j) := by
  decide +kernel

/-- The row operations of every step compute its word on the 24 basis masks. -/
theorem sixthBitsetStage_basis_words (s : ℕ) (hs : s < 5) :
    ∀ p ∈ (sixthBitsetStageOps s).zip (sixthBitsetStageWords s), ∀ j < 24,
      tenthForestOpsMap p.1 (2 ^ j) = sixthBitsetWordApply p.2 (2 ^ j) := by
  match s, hs with
  | 0, _ => exact sixthBitsetStage_basis_words_0
  | 1, _ => exact sixthBitsetStage_basis_words_1
  | 2, _ => exact sixthBitsetStage_basis_words_2
  | 3, _ => exact sixthBitsetStage_basis_words_3
  | 4, _ => exact sixthBitsetStage_basis_words_4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
