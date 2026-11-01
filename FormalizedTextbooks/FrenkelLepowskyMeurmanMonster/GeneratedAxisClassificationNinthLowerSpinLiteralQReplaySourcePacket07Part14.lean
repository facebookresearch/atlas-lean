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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 : Fin 17 → Array ℕ :=
  ![
    #[14841303, 31543246, 6332427, 27669735, 20728717, 9909031, 5244932, 29926275,
      1297584, 23009186, 18050075, 4956160, 23549115, 21417061, 20208764, 3798117,
      19894494, 197325, 19452435, 22070902, 2564295, 21875899, 2832915, 11834948],
    #[28239648, 12491804, 24086273, 14532152, 24971466, 11958826, 5747200, 28516548,
      20996231, 488894, 19023720, 1495040, 23904134, 4008959, 3219915, 20956159,
      18517113, 17257803, 19478834, 25156301, 18052685, 25094022, 4395314, 13388767],
    #[27391166, 28212252, 23430738, 14157973, 22302548, 10153849, 23355597, 26584228,
      6956500, 20215571, 725142, 454656, 5901190, 977234, 480715, 17437010,
      17369812, 18940235, 18545567, 7932621, 1275469, 6185862, 7734175, 30361874],
    #[32196745, 10068329, 5635306, 26300413, 4409056, 16103112, 7953475, 25853628,
      3205921, 5366884, 3984380, 7155712, 7712715, 950452, 23296539, 18917556,
      22509439, 8139392, 42495, 21663051, 5635536, 616395, 23936511, 12209201],
    #[30948900, 28321527, 24947476, 12287662, 4625453, 15728741, 24350064, 11504657,
      3815954, 7446628, 329730, 8110080, 21367046, 3019988, 7134597, 18877652,
      24266194, 24764493, 3569055, 21641547, 25103491, 17563910, 24972703, 26853116],
    #[30618493, 9927435, 17292855, 33252794, 3855482, 26404781, 3709391, 11713894,
      23546941, 4311714, 19339534, 2932736, 20085258, 7565861, 8384144, 20085285,
      24743983, 2097290, 3166373, 8370816, 23587994, 24470026, 17602725, 16765962],
    #[31502490, 14765837, 17908551, 14990221, 22151877, 14989503, 20560969, 10780410,
      18063425, 422120, 262410, 7319552, 2407174, 17322528, 17778088, 612896,
      3199270, 1226439, 51169, 5815745, 22120110, 2138886, 19009505, 11538012],
    #[15170300, 11972689, 19491464, 16554186, 20053579, 30820820, 6878936, 32296708,
      7885194, 4904811, 17920778, 1531904, 23814914, 20862255, 19879608, 8342831,
      5406253, 6417175, 19391802, 22870037, 3354042, 19753730, 216378, 11379940],
    #[14972977, 8614556, 1707077, 14016340, 19446197, 16391303, 23810165, 12949754,
      7014215, 7954886, 1165066, 1531904, 22897410, 2663727, 17563669, 21581103,
      24284717, 6593978, 3433367, 5209784, 17206039, 19643138, 19319703, 9122020],
    #[33133843, 11892986, 1542104, 33187552, 6941406, 26277530, 21265302, 31842910,
      3972826, 17326662, 22462032, 3387392, 22311170, 1305712, 25111348, 20804720,
      24212850, 23798669, 19150591, 19034767, 16777782, 20691202, 3837695, 32630379],
    #[27098476, 29823582, 299817, 16097585, 23608689, 15919014, 5030896, 30353848,
      19436323, 17608323, 20256228, 1179648, 6031370, 16924875, 22209040, 6031563,
      20160705, 17735882, 21757963, 18802880, 8233498, 7446538, 5285899, 26639097],
    #[27769951, 15463181, 18351642, 30061263, 5320431, 32789446, 21303310, 29592811,
      18715118, 2329885, 19894487, 1314816, 4542452, 20850168, 23535837, 4234744,
      3170828, 18954068, 21013848, 17750176, 21485353, 7272436, 8007000, 28376729],
    #[26222845, 33400053, 19666376, 11763064, 24254631, 27773061, 4788238, 12257711,
      1855660, 19136575, 2702400, 7839744, 5197156, 6004320, 23127362, 17229408,
      18205444, 2266634, 24829198, 21433198, 811046, 6591844, 7116046, 9058420],
    #[9773648, 15606360, 3555483, 26814539, 6184340, 11705896, 21418992, 26999215,
      19562700, 2670860, 597024, 5722112, 22222935, 21916845, 4442095, 1426605,
      20733178, 17302329, 5185475, 5761902, 1390520, 21938263, 22632387, 9215092],
    #[8775924, 32195320, 23829632, 9534783, 6798465, 9689047, 4483990, 12743825,
      20908431, 16974604, 6567391, 7110656, 19766543, 18690157, 4018347, 4626541,
      20075874, 4891880, 23044490, 5249511, 23459236, 19412239, 3287434, 9706531],
    #[26555026, 25645462, 20039345, 13465872, 7735628, 11801526, 6570101, 12587644,
      6336176, 20085512, 18735550, 2285568, 23265281, 1082652, 3368337, 21703964,
      17018141, 7998812, 6963265, 23088477, 6958480, 16779265, 17410113, 10402092],
    #[11531169, 25438043, 17237681, 16234531, 23738399, 25327574, 22542040, 31662257,
      23297053, 18558198, 18408211, 311296, 20980396, 17589295, 17606159, 5315631,
      1875587, 20978703, 4813452, 5869219, 22080675, 17156780, 18635404, 11688063]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part14 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (13, true),
  (12, true), (12, true), (12, true), (13, true),
  (12, true), (12, true), (13, true), (12, false),
  (13, false), (12, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part14.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_224 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5376 5400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_224 :
    generatedNinthLowerSpinSourceQReplayWord 7 224 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 0)
    5376 24 0 (prefix_sizes 0) slice_224
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_225 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5400 5424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_225 :
    generatedNinthLowerSpinSourceQReplayWord 7 225 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 1)
    5400 24 0 (prefix_sizes 1) slice_225
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_226 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5424 5448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_226 :
    generatedNinthLowerSpinSourceQReplayWord 7 226 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 2)
    5424 24 0 (prefix_sizes 2) slice_226
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_227 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5448 5472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_227 :
    generatedNinthLowerSpinSourceQReplayWord 7 227 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 3)
    5448 24 0 (prefix_sizes 3) slice_227
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_228 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5472 5496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_228 :
    generatedNinthLowerSpinSourceQReplayWord 7 228 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 4)
    5472 24 0 (prefix_sizes 4) slice_228
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_229 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5496 5520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_229 :
    generatedNinthLowerSpinSourceQReplayWord 7 229 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 5)
    5496 24 0 (prefix_sizes 5) slice_229
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_230 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5520 5544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_230 :
    generatedNinthLowerSpinSourceQReplayWord 7 230 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 6)
    5520 24 0 (prefix_sizes 6) slice_230
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_231 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5544 5568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_231 :
    generatedNinthLowerSpinSourceQReplayWord 7 231 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 7)
    5544 24 0 (prefix_sizes 7) slice_231
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_232 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5568 5592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_232 :
    generatedNinthLowerSpinSourceQReplayWord 7 232 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 8)
    5568 24 0 (prefix_sizes 8) slice_232
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_233 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5592 5616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_233 :
    generatedNinthLowerSpinSourceQReplayWord 7 233 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 9)
    5592 24 0 (prefix_sizes 9) slice_233
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_234 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5616 5640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_234 :
    generatedNinthLowerSpinSourceQReplayWord 7 234 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 10)
    5616 24 0 (prefix_sizes 10) slice_234
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_235 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5640 5664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_235 :
    generatedNinthLowerSpinSourceQReplayWord 7 235 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 11)
    5640 24 0 (prefix_sizes 11) slice_235
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_236 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5664 5688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_236 :
    generatedNinthLowerSpinSourceQReplayWord 7 236 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 12)
    5664 24 0 (prefix_sizes 12) slice_236
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_237 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5688 5712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_237 :
    generatedNinthLowerSpinSourceQReplayWord 7 237 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 13)
    5688 24 0 (prefix_sizes 13) slice_237
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_238 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5712 5736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_238 :
    generatedNinthLowerSpinSourceQReplayWord 7 238 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 14)
    5712 24 0 (prefix_sizes 14) slice_238
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_239 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5736 5760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_239 :
    generatedNinthLowerSpinSourceQReplayWord 7 239 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 15)
    5736 24 0 (prefix_sizes 15) slice_239
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_240 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5760 5784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_14_240 :
    generatedNinthLowerSpinSourceQReplayWord 7 240 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part14 16)
    5760 24 0 (prefix_sizes 16) slice_240
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 224 240 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_14 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨224 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part14.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part14
    224 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (224 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
