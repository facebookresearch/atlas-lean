/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinLiteralQReplaySourceGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayData

/-! Only the complete original prefixes and actual signed letters in this source block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Small arrays retain every original base bit and true central bit. -/
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 : Fin 11 → Array ℕ :=
  ![
    #[15851414, 4808360, 5176230, 11099668, 4466210, 26146563, 5175193, 5571934,
      11863076, 23860457, 7896449, 6902296, 30486402, 11042780, 23892025, 15140891,
      19730526, 9870617, 12998352, 7595844, 28922468, 11096669, 9805268, 29106887],
    #[25638795, 20225688, 5540196, 33263046, 1222357, 29074181, 868472, 24557324,
      13583571, 1319585, 8354112, 3899704, 10755511, 26168649, 2829536, 32124367,
      704766, 29522227, 16016965, 5317946, 15538409, 14382089, 31031105, 16709492],
    #[9593126, 16902229, 25091159, 13511531, 16970453, 9958998, 2823288, 24753394,
      12948960, 311969, 5478419, 16901227, 8690103, 11991735, 1912032, 15347151,
      3392256, 30578995, 29672005, 21128087, 30297668, 15205028, 14909042, 14786698],
    #[27299887, 17960449, 18324209, 25317142, 17389386, 32105736, 20461347, 22525806,
      13694812, 4674711, 22308803, 735456, 29429165, 31917477, 7954256, 30747278,
      17631240, 25992686, 14110005, 24098696, 11619638, 14901862, 12492325, 27402317],
    #[12214556, 1236577, 3238545, 9702166, 3793706, 31805499, 19727854, 5732206,
      14673090, 21832132, 5743886, 2955488, 32042579, 31371867, 22461646, 33541053,
      18566152, 12164899, 13552331, 22024310, 28453787, 13236053, 27843109, 26292864],
    #[12559423, 2881783, 5528821, 13926201, 20063781, 27289373, 19661107, 5879026,
      12932368, 1856328, 7654744, 16872555, 11459045, 25427639, 20474896, 29833430,
      19502930, 30411896, 16008773, 7501719, 31006719, 31392751, 16329248, 31860161],
    #[11680079, 3894865, 23177997, 10721869, 22767218, 16405610, 4863257, 18375948,
      29200749, 21514121, 8089320, 2356209, 32959072, 12218254, 5967977, 10088313,
      1725934, 16284619, 9336528, 21095085, 27300111, 25203046, 10849583, 15011861],
    #[27449679, 2854481, 7039582, 25406029, 4282177, 13829012, 7684743, 1352767,
      11698931, 22155994, 8308773, 3089058, 30742701, 27021198, 23619268, 11758122,
      17786659, 32374022, 29193341, 7807661, 26624367, 10737579, 28667183, 31897272],
    #[27533440, 22862059, 7737784, 28873090, 25036244, 32877310, 6648768, 1657167,
      12498265, 1838961, 6087464, 2287848, 10654945, 11702425, 263958, 30058273,
      1909880, 31190616, 33481924, 21607913, 29349031, 27104177, 27087984, 15342223],
    #[15506633, 22168426, 20414161, 9737411, 24750881, 15769942, 3186752, 1097856,
      8674279, 21142984, 17995563, 1285995, 15840566, 14878461, 18023275, 15791478,
      18056139, 31387364, 28524062, 2459442, 15868605, 30499286, 16337099, 8446144],
    #[14683369, 5393258, 1191633, 27264227, 24118049, 14705014, 64, 128,
      8479687, 4431304, 2307883, 17997675, 13751574, 30582493, 1180523, 14693718,
      148427, 12828356, 11992638, 3727154, 32711325, 30499318, 31510763, 10514656]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part23 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, true), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (5, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 11,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part23.size = 10 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_368 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8832 8856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_368 :
    generatedNinthLowerSpinSourceQReplayWord 7 368 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 0)
    8832 24 0 (prefix_sizes 0) slice_368
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_369 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8856 8880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_369 :
    generatedNinthLowerSpinSourceQReplayWord 7 369 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 1)
    8856 24 0 (prefix_sizes 1) slice_369
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_370 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8880 8904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_370 :
    generatedNinthLowerSpinSourceQReplayWord 7 370 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 2)
    8880 24 0 (prefix_sizes 2) slice_370
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_371 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8904 8928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_371 :
    generatedNinthLowerSpinSourceQReplayWord 7 371 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 3)
    8904 24 0 (prefix_sizes 3) slice_371
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_372 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8928 8952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_372 :
    generatedNinthLowerSpinSourceQReplayWord 7 372 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 4)
    8928 24 0 (prefix_sizes 4) slice_372
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_373 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8952 8976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_373 :
    generatedNinthLowerSpinSourceQReplayWord 7 373 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 5)
    8952 24 0 (prefix_sizes 5) slice_373
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_374 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8976 9000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_374 :
    generatedNinthLowerSpinSourceQReplayWord 7 374 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 6)
    8976 24 0 (prefix_sizes 6) slice_374
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_375 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 9000 9024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_375 :
    generatedNinthLowerSpinSourceQReplayWord 7 375 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 7)
    9000 24 0 (prefix_sizes 7) slice_375
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (9000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_376 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 9024 9048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_376 :
    generatedNinthLowerSpinSourceQReplayWord 7 376 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 8)
    9024 24 0 (prefix_sizes 8) slice_376
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (9024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_377 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 9048 9072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_377 :
    generatedNinthLowerSpinSourceQReplayWord 7 377 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 9)
    9048 24 0 (prefix_sizes 9) slice_377
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (9048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_378 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 9072 9096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_23_378 :
    generatedNinthLowerSpinSourceQReplayWord 7 378 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part23 10)
    9072 24 0 (prefix_sizes 10) slice_378
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (9072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 368 378 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part23 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_23 :
    (fun n : Fin 10 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨368 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part23.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part23
    368 10 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (368 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
