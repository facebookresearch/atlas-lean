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
def generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 : Fin 15 → Array ℕ :=
  ![
    #[21791051, 21268340, 6826884, 17756885, 6751839, 2512159, 17155490, 4018288,
      5338580, 7262784, 17566525, 2048, 23920640, 4427776, 4222976, 16814080,
      22773760, 1112064, 2510848, 21049344, 7254016, 6160384, 2551808, 12637471],
    #[6976128, 2224839, 6180549, 5464688, 21373157, 3198060, 2124982, 20249753,
      973601, 7210381, 16839711, 2048, 21934080, 1110016, 8048640, 22208512,
      18055168, 3098624, 3821568, 21180416, 5664768, 4616192, 2785280, 13257836],
    #[3720641, 19992389, 23187993, 4003217, 24124260, 2760176, 2669449, 22469295,
      4995364, 7093648, 23397736, 2048, 17940480, 3096576, 6799360, 19288064,
      18317312, 3491840, 8331264, 16785408, 3710976, 7720960, 1589248, 9825776],
    #[23171093, 1894356, 20767548, 5013675, 1102510, 23581958, 4489930, 474343,
      5412643, 23127460, 6096628, 2048, 19685376, 3489792, 6926336, 20598784,
      22777856, 8337408, 585728, 21504000, 6160384, 7192576, 7442432, 28308742],
    #[6563512, 3498058, 18157730, 22025624, 17622013, 22311883, 5175193, 2996660,
      6374894, 23888119, 22569017, 2048, 20598784, 1269760, 7950336, 19685376,
      24997888, 7329792, 585728, 24702976, 6209536, 5963776, 4276224, 28083147],
    #[5522856, 3975874, 20357216, 427905, 20490091, 2823288, 868472, 49502,
      18343762, 17684065, 2129120, 2048, 19288064, 2600960, 2834432, 17940480,
      18903040, 7981056, 8331264, 16793600, 499712, 3252224, 1581056, 9733240],
    #[8306939, 20343697, 20357216, 17581778, 19788230, 868472, 2823288, 3392499,
      17241906, 1910273, 2129120, 2048, 19288064, 2600960, 876544, 17940480,
      16793600, 7931904, 6279168, 18903040, 1540096, 2195456, 3674112, 9625720],
    #[1594721, 460170, 17340897, 20227403, 129, 23728349, 20461347, 5109605,
      7099881, 7733255, 5574480, 2048, 22208512, 7327744, 5242880, 21934080,
      18231296, 3303424, 4829184, 22728704, 1277952, 6877184, 3366912, 25784541],
    #[112383, 3449671, 1145471, 17088843, 18211372, 6935056, 19727854, 4280886,
      7541367, 8156500, 21818574, 2048, 21237760, 8335360, 4251648, 22958080,
      18231296, 2381824, 7954432, 21766144, 2457600, 4718592, 3502080, 10240528],
    #[6176779, 785032, 1450128, 1475200, 16839727, 2757939, 19661107, 17711642,
      1610640, 17151976, 16841744, 2048, 17174528, 188416, 2633728, 20221952,
      16793600, 7948288, 8323072, 16789504, 1196032, 262144, 3997696, 9827635],
    #[21395201, 22828737, 676082, 1582529, 24053108, 24113483, 4863257, 6393661,
      22102270, 21152565, 4661353, 2048, 17108992, 2830336, 4296704, 18100224,
      24702976, 3614720, 4247552, 21114880, 7770112, 4984832, 4444160, 28164427],
    #[24929874, 22828737, 19116812, 20039231, 5464135, 24737099, 7684743, 24870414,
      25080576, 6182406, 21124804, 2048, 16973824, 856064, 4280320, 16908288,
      21504000, 3614720, 7340032, 24440832, 6713344, 8048640, 7671808, 26051915],
    #[7711978, 7471129, 7713036, 6570055, 23628420, 19879634, 6648768, 18589012,
      1163276, 6547028, 427798, 2048, 16908288, 4390912, 7593984, 21172224,
      21766144, 849920, 4902912, 23392256, 3301376, 6799360, 5095424, 31553234],
    #[19061303, 22997556, 7387140, 23362180, 21182401, 20787235, 3186752, 6690792,
      811264, 18540516, 17359723, 2048, 21172224, 4329472, 2158592, 21495808,
      16789504, 6961152, 7143424, 19496960, 7929856, 6926336, 2686976, 30720035],
    #[780855, 6543924, 4829188, 21590660, 23787457, 19476515, 64, 23320552,
      256, 731108, 17427307, 2048, 4397056, 21108736, 2158592, 21495808,
      16789504, 23736320, 7143424, 19496960, 7929856, 6926336, 2686976, 29372419]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters00Part10 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (12, true), (13, true),
  (12, false), (13, true), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (5, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 15,
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters00Part10.size = 14 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_160 :
    generatedNinthLowerSpinSourceQReplayWord 0 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 0)
    3840 24 0 (prefix_sizes 0) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_161 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3864 3888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_161 :
    generatedNinthLowerSpinSourceQReplayWord 0 161 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 1)
    3864 24 0 (prefix_sizes 1) slice_161
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_162 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3888 3912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_162 :
    generatedNinthLowerSpinSourceQReplayWord 0 162 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 2)
    3888 24 0 (prefix_sizes 2) slice_162
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_163 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3912 3936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_163 :
    generatedNinthLowerSpinSourceQReplayWord 0 163 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 3)
    3912 24 0 (prefix_sizes 3) slice_163
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_164 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3936 3960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_164 :
    generatedNinthLowerSpinSourceQReplayWord 0 164 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 4)
    3936 24 0 (prefix_sizes 4) slice_164
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_165 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3960 3984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_165 :
    generatedNinthLowerSpinSourceQReplayWord 0 165 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 5)
    3960 24 0 (prefix_sizes 5) slice_165
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_166 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3984 4008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_166 :
    generatedNinthLowerSpinSourceQReplayWord 0 166 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 6)
    3984 24 0 (prefix_sizes 6) slice_166
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_167 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4008 4032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_167 :
    generatedNinthLowerSpinSourceQReplayWord 0 167 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 7)
    4008 24 0 (prefix_sizes 7) slice_167
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_168 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4032 4056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_168 :
    generatedNinthLowerSpinSourceQReplayWord 0 168 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 8)
    4032 24 0 (prefix_sizes 8) slice_168
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_169 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4056 4080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_169 :
    generatedNinthLowerSpinSourceQReplayWord 0 169 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 9)
    4056 24 0 (prefix_sizes 9) slice_169
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_170 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4080 4104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_170 :
    generatedNinthLowerSpinSourceQReplayWord 0 170 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 10)
    4080 24 0 (prefix_sizes 10) slice_170
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_171 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4104 4128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_171 :
    generatedNinthLowerSpinSourceQReplayWord 0 171 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 11)
    4104 24 0 (prefix_sizes 11) slice_171
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_172 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4128 4152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_172 :
    generatedNinthLowerSpinSourceQReplayWord 0 172 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 12)
    4128 24 0 (prefix_sizes 12) slice_172
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_173 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4152 4176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_173 :
    generatedNinthLowerSpinSourceQReplayWord 0 173 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 13)
    4152 24 0 (prefix_sizes 13) slice_173
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_174 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 4176 4200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_10_174 :
    generatedNinthLowerSpinSourceQReplayWord 0 174 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part10 14)
    4176 24 0 (prefix_sizes 14) slice_174
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (4176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords00.extract 160 174 =
      generatedNinthLowerSpinLiteralQReplayLetters00Part10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_00_part_10 :
    (fun n : Fin 14 =>
      generatedNinthLowerSpinSourceQReplayLetter 0 ⟨160 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters00Part10.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords00
    generatedNinthLowerSpinLiteralQReplayLetters00Part10
    160 14 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords00.getD (160 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
