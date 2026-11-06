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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 : Fin 17 → Array ℕ :=
  ![
    #[29760365, 33141485, 5042328, 11211805, 24915727, 27370022, 1765822, 13147097,
      376926, 5929599, 2457735, 4317184, 6572230, 18751562, 7889037, 3500106,
      2302092, 8377444, 6796520, 24198306, 7127115, 7839942, 23231720, 10791419],
    #[27112724, 14152791, 17694835, 28391475, 7866373, 11376679, 21188700, 9657414,
      20320510, 787750, 19475632, 7479296, 23578765, 23354050, 4220338, 3973826,
      2558543, 20944659, 7396700, 24285086, 19199295, 23675021, 21419356, 8580461],
    #[12565966, 10924785, 17892898, 32214498, 6053617, 27654110, 2372592, 11818556,
      4481936, 20789201, 16854944, 4149248, 18668978, 4696453, 2430114, 21438853,
      20290615, 18808885, 25132034, 3935623, 23257360, 24307122, 263170, 27917038],
    #[26001251, 28332689, 4056945, 32415535, 22826641, 11786174, 17633294, 28415121,
      23953518, 17942242, 4074558, 2056192, 19468063, 5119515, 20772668, 24028699,
      19466500, 17450744, 4222972, 18651623, 23605283, 22533919, 19785724, 11918301],
    #[26222845, 33400053, 19666376, 11763064, 24254631, 27773061, 4788238, 12257711,
      1855660, 19136575, 2702400, 7839744, 5197156, 6004320, 23127362, 17229408,
      18205444, 2266634, 24829198, 21433198, 811046, 6591844, 7116046, 9058420],
    #[27769951, 15463181, 18351642, 30061263, 5320431, 32789446, 21303310, 29592811,
      18715118, 2329885, 19894487, 1314816, 4542452, 20850168, 23535837, 4234744,
      3170828, 18954068, 21013848, 17750176, 21485353, 7272436, 8007000, 28376729],
    #[27098476, 29823582, 299817, 16097585, 23608689, 15919014, 5030896, 30353848,
      19436323, 17608323, 20256228, 1179648, 6031370, 16924875, 22209040, 6031563,
      20160705, 17735882, 21757963, 18802880, 8233498, 7446538, 5285899, 26639097],
    #[33133843, 11892986, 1542104, 33187552, 6941406, 26277530, 21265302, 31842910,
      3972826, 17326662, 22462032, 3387392, 22311170, 1305712, 25111348, 20804720,
      24212850, 23798669, 19150591, 19034767, 16777782, 20691202, 3837695, 32630379],
    #[14972977, 8614556, 1707077, 14016340, 19446197, 16391303, 23810165, 12949754,
      7014215, 7954886, 1165066, 1531904, 22897410, 2663727, 17563669, 21581103,
      24284717, 6593978, 3433367, 5209784, 17206039, 19643138, 19319703, 9122020],
    #[15170300, 11972689, 19491464, 16554186, 20053579, 30820820, 6878936, 32296708,
      7885194, 4904811, 17920778, 1531904, 23814914, 20862255, 19879608, 8342831,
      5406253, 6417175, 19391802, 22870037, 3354042, 19753730, 216378, 11379940],
    #[31502490, 14765837, 17908551, 14990221, 22151877, 14989503, 20560969, 10780410,
      18063425, 422120, 262410, 7319552, 2407174, 17322528, 17778088, 612896,
      3199270, 1226439, 51169, 5815745, 22120110, 2138886, 19009505, 11538012],
    #[30618493, 9927435, 17292855, 33252794, 3855482, 26404781, 3709391, 11713894,
      23546941, 4311714, 19339534, 2932736, 20085258, 7565861, 8384144, 20085285,
      24743983, 2097290, 3166373, 8370816, 23587994, 24470026, 17602725, 16765962],
    #[30948900, 28321527, 24947476, 12287662, 4625453, 15728741, 24350064, 11504657,
      3815954, 7446628, 329730, 8110080, 21367046, 3019988, 7134597, 18877652,
      24266194, 24764493, 3569055, 21641547, 25103491, 17563910, 24972703, 26853116],
    #[32196745, 10068329, 5635306, 26300413, 4409056, 16103112, 7953475, 25853628,
      3205921, 5366884, 3984380, 7155712, 7712715, 950452, 23296539, 18917556,
      22509439, 8139392, 42495, 21663051, 5635536, 616395, 23936511, 12209201],
    #[27391166, 28212252, 23430738, 14157973, 22302548, 10153849, 23355597, 26584228,
      6956500, 20215571, 725142, 454656, 5901190, 977234, 480715, 17437010,
      17369812, 18940235, 18545567, 7932621, 1275469, 6185862, 7734175, 30361874],
    #[28239648, 12491804, 24086273, 14532152, 24971466, 11958826, 5747200, 28516548,
      20996231, 488894, 19023720, 1495040, 23904134, 4008959, 3219915, 20956159,
      18517113, 17257803, 19478834, 25156301, 18052685, 25094022, 4395314, 13388767],
    #[14841303, 31543246, 6332427, 27669735, 20728717, 9909031, 5244932, 29926275,
      1297584, 23009186, 18050075, 4956160, 23549115, 21417061, 20208764, 3798117,
      19894494, 197325, 19452435, 22070902, 2564295, 21875899, 2832915, 11834948]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part13 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, false), (13, true), (12, true),
  (12, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false),
  (13, false), (12, false), (13, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part13.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_208 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4992 5016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_208 :
    generatedNinthLowerSpinSourceQReplayWord 7 208 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 0)
    4992 24 0 (prefix_sizes 0) slice_208
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_209 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5016 5040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_209 :
    generatedNinthLowerSpinSourceQReplayWord 7 209 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 1)
    5016 24 0 (prefix_sizes 1) slice_209
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_210 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5040 5064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_210 :
    generatedNinthLowerSpinSourceQReplayWord 7 210 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 2)
    5040 24 0 (prefix_sizes 2) slice_210
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_211 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5064 5088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_211 :
    generatedNinthLowerSpinSourceQReplayWord 7 211 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 3)
    5064 24 0 (prefix_sizes 3) slice_211
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_212 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5088 5112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_212 :
    generatedNinthLowerSpinSourceQReplayWord 7 212 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 4)
    5088 24 0 (prefix_sizes 4) slice_212
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_213 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5112 5136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_213 :
    generatedNinthLowerSpinSourceQReplayWord 7 213 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 5)
    5112 24 0 (prefix_sizes 5) slice_213
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_214 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5136 5160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_214 :
    generatedNinthLowerSpinSourceQReplayWord 7 214 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 6)
    5136 24 0 (prefix_sizes 6) slice_214
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_215 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5160 5184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_215 :
    generatedNinthLowerSpinSourceQReplayWord 7 215 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 7)
    5160 24 0 (prefix_sizes 7) slice_215
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_216 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5184 5208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_216 :
    generatedNinthLowerSpinSourceQReplayWord 7 216 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 8)
    5184 24 0 (prefix_sizes 8) slice_216
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_217 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5208 5232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_217 :
    generatedNinthLowerSpinSourceQReplayWord 7 217 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 9)
    5208 24 0 (prefix_sizes 9) slice_217
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_218 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5232 5256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_218 :
    generatedNinthLowerSpinSourceQReplayWord 7 218 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 10)
    5232 24 0 (prefix_sizes 10) slice_218
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_219 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5256 5280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_219 :
    generatedNinthLowerSpinSourceQReplayWord 7 219 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 11)
    5256 24 0 (prefix_sizes 11) slice_219
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_220 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5280 5304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_220 :
    generatedNinthLowerSpinSourceQReplayWord 7 220 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 12)
    5280 24 0 (prefix_sizes 12) slice_220
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_221 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5304 5328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_221 :
    generatedNinthLowerSpinSourceQReplayWord 7 221 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 13)
    5304 24 0 (prefix_sizes 13) slice_221
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_222 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5328 5352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_222 :
    generatedNinthLowerSpinSourceQReplayWord 7 222 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 14)
    5328 24 0 (prefix_sizes 14) slice_222
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_223 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5352 5376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_223 :
    generatedNinthLowerSpinSourceQReplayWord 7 223 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 15)
    5352 24 0 (prefix_sizes 15) slice_223
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_224 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5376 5400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_13_224 :
    generatedNinthLowerSpinSourceQReplayWord 7 224 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part13 16)
    5376 24 0 (prefix_sizes 16) slice_224
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 208 224 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_13 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨208 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part13.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part13
    208 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (208 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
