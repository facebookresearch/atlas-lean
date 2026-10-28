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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 : Fin 11 → Array ℕ :=
  ![
    #[10877820, 31954140, 10492241, 23105773, 29845770, 21127731, 5175193, 16780820,
      11022917, 32167825, 17680441, 2676736, 24940120, 130648, 17436766, 2174016,
      19476480, 647956, 134744, 7280468, 6052894, 19586112, 8296716, 32310631],
    #[9677273, 33168705, 15742721, 18226259, 12636430, 19967462, 868472, 1097158,
      28294453, 31894132, 3986656, 3987456, 17689862, 2989318, 254, 4013118,
      16900096, 18973236, 1883398, 23705098, 18701504, 16784446, 19827468, 32754668],
    #[27008551, 30748351, 15341138, 3947872, 15926211, 1305387, 2823288, 17038187,
      25619147, 14011577, 1766624, 3852288, 17337291, 576459, 983808, 3424160,
      16900096, 20055193, 654283, 7725881, 17530016, 20914080, 20015346, 15398930],
    #[12437540, 8767575, 25197572, 2209299, 10215028, 4668630, 20461347, 4693782,
      30313588, 31890001, 4409168, 30720, 6528120, 24489080, 21395464, 4519064,
      20787200, 358512, 24677496, 21820648, 19188880, 21611672, 19167376, 8599614],
    #[12287044, 25787748, 25217028, 20485517, 26106041, 23636808, 19727854, 22481686,
      32426100, 30448209, 22717646, 30720, 4524152, 22231160, 24566792, 7487640,
      20652032, 2316400, 22546552, 21647592, 18009232, 21590168, 17987728, 11144096],
    #[11078359, 31637492, 30409216, 20757904, 13501146, 2932617, 19661107, 20758329,
      10059417, 13634745, 20608016, 3852288, 3280793, 20074393, 20301650, 17558514,
      17100800, 20092057, 20344729, 21686123, 17743008, 330738, 20228338, 15378658],
    #[12073854, 25454094, 27318536, 3503524, 33144689, 2639512, 4863257, 23788109,
      28128167, 31082120, 1185897, 3000320, 19999395, 4840099, 2999790, 17754450,
      19800064, 23659183, 5106339, 25023485, 8064188, 3004754, 8132958, 9794917],
    #[26741630, 10377021, 29133883, 1036535, 14917154, 3870805, 7684743, 4852301,
      26129770, 13615173, 17940164, 1820672, 3684701, 24123741, 20510499, 4008959,
      17698816, 20980049, 24263005, 6365870, 24972508, 18353151, 4836339, 25834235],
    #[10921115, 32929869, 27446095, 7923281, 16775283, 4073393, 6648768, 4686210,
      8828922, 12446602, 6410006, 2844672, 17006005, 5201333, 726136, 19076445,
      21037056, 2598069, 4484533, 649704, 839973, 2196829, 23983197, 9469529],
    #[27956129, 13777034, 27875720, 23290091, 26204312, 17044868, 3186752, 24413379,
      29740544, 31387339, 20556651, 3241984, 23633548, 6860428, 18072523, 6349287,
      16842752, 4493192, 7114380, 18847343, 22188588, 24187367, 17721571, 10630123],
    #[11731841, 33161386, 26739112, 24772843, 28448952, 2211204, 64, 4252867,
      29490720, 12828395, 20489067, 3241984, 23633548, 6860428, 132043, 6416871,
      16842752, 24242056, 7114380, 19660399, 4348460, 24123879, 20578531, 11731915]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part19 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, true), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (5, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 11,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part19.size = 10 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_304 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7296 7320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_304 :
    generatedNinthLowerSpinSourceQReplayWord 5 304 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 0)
    7296 24 0 (prefix_sizes 0) slice_304
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_305 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7320 7344 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_305 :
    generatedNinthLowerSpinSourceQReplayWord 5 305 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 1)
    7320 24 0 (prefix_sizes 1) slice_305
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7320 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_306 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7344 7368 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_306 :
    generatedNinthLowerSpinSourceQReplayWord 5 306 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 2)
    7344 24 0 (prefix_sizes 2) slice_306
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7344 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_307 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7368 7392 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_307 :
    generatedNinthLowerSpinSourceQReplayWord 5 307 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 3)
    7368 24 0 (prefix_sizes 3) slice_307
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7368 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_308 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7392 7416 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_308 :
    generatedNinthLowerSpinSourceQReplayWord 5 308 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 4)
    7392 24 0 (prefix_sizes 4) slice_308
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7392 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_309 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7416 7440 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_309 :
    generatedNinthLowerSpinSourceQReplayWord 5 309 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 5)
    7416 24 0 (prefix_sizes 5) slice_309
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7416 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_310 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7440 7464 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_310 :
    generatedNinthLowerSpinSourceQReplayWord 5 310 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 6)
    7440 24 0 (prefix_sizes 6) slice_310
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7440 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_311 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7464 7488 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_311 :
    generatedNinthLowerSpinSourceQReplayWord 5 311 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 7)
    7464 24 0 (prefix_sizes 7) slice_311
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7464 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_312 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7488 7512 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_312 :
    generatedNinthLowerSpinSourceQReplayWord 5 312 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 8)
    7488 24 0 (prefix_sizes 8) slice_312
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7488 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_313 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7512 7536 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_313 :
    generatedNinthLowerSpinSourceQReplayWord 5 313 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 9)
    7512 24 0 (prefix_sizes 9) slice_313
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7512 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_314 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7536 7560 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_19_314 :
    generatedNinthLowerSpinSourceQReplayWord 5 314 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part19 10)
    7536 24 0 (prefix_sizes 10) slice_314
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7536 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 304 314 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part19 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_19 :
    (fun n : Fin 10 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨304 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part19.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part19
    304 10 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (304 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
