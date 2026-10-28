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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 : Fin 3 → Array ℕ :=
  ![
    #[9783313, 4305981, 4790108, 1947792, 8527767, 20782187, 6648768, 25622245,
      14375234, 20175746, 1456128, 4577512, 14186230, 12786278, 21307158, 32585014,
      18238608, 30225575, 8672979, 566761, 27854424, 30038350, 9291367, 19252722],
    #[29337908, 3745857, 5182944, 2009330, 26294957, 1174513, 3186752, 26703422,
      29047951, 509387, 18432, 1580907, 9311748, 9796260, 1579883, 11834948,
      18504864, 9683645, 12483884, 19830578, 29296356, 9919887, 29133817, 23976968],
    #[25872660, 557121, 23272928, 19609842, 26264205, 3724273, 64, 9614878,
      27985071, 18007499, 18432, 1644395, 28517924, 12092036, 1643371, 12127844,
      693408, 26395293, 27714828, 3393330, 10639044, 25888175, 28855257, 21025800]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part15 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (5, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 3,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part15.size = 2 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_240 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5760 5784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_15_240 :
    generatedNinthLowerSpinSourceQReplayWord 6 240 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 0)
    5760 24 0 (prefix_sizes 0) slice_240
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_241 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5784 5808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_15_241 :
    generatedNinthLowerSpinSourceQReplayWord 6 241 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 1)
    5784 24 0 (prefix_sizes 1) slice_241
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_242 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5808 5832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_15_242 :
    generatedNinthLowerSpinSourceQReplayWord 6 242 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part15 2)
    5808 24 0 (prefix_sizes 2) slice_242
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 240 242 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_15 :
    (fun n : Fin 2 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨240 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part15.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part15
    240 2 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (240 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
