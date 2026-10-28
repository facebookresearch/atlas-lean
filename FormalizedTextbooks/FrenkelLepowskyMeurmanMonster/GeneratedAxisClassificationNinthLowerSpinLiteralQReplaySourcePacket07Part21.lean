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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 : Fin 17 → Array ℕ :=
  ![
    #[13489142, 9204421, 401871, 28506917, 4623125, 25674222, 5891800, 15975195,
      24328233, 23371829, 20059595, 17668096, 4227558, 20025189, 2955479, 4552549,
      2217603, 23357253, 6928838, 22908579, 22573361, 19718630, 19407302, 27043358],
    #[32196598, 25953989, 18923983, 10403350, 24915526, 8700707, 21651573, 14697910,
      4218596, 22480632, 19022283, 17532928, 21182251, 17558070, 105956, 4837942,
      20509981, 21553782, 24788843, 4353373, 6386383, 3778347, 3893099, 9877293],
    #[29970176, 16615961, 4338761, 14991983, 22168273, 12705834, 16837526, 8911501,
      4870961, 1971722, 16977481, 18802688, 6098808, 5478938, 6394685, 17998362,
      17591650, 18763423, 22875133, 18651623, 22230085, 21118840, 3073021, 31425654],
    #[12397662, 10595132, 20762328, 14951595, 18225264, 10286633, 1188848, 9200078,
      1903903, 24840020, 7905232, 24004608, 1145799, 17819453, 1879071, 5037885,
      20952314, 24840361, 4621395, 21433198, 17870808, 18103239, 23493715, 27300805],
    #[11808704, 11434146, 2726005, 29925784, 18225264, 25977385, 17502222, 28930915,
      4058495, 5390538, 5733454, 25077760, 18144522, 1431054, 17857868, 24120846,
      16782084, 5787236, 23881056, 5761902, 18860102, 503050, 5021024, 10151670],
    #[32365945, 10618976, 23213088, 14692479, 22168273, 14137300, 4259854, 11652378,
      3099344, 2929549, 17853488, 22177792, 2586352, 4837364, 6663986, 20908020,
      18915588, 5490455, 21446163, 5249511, 23683522, 17815280, 3462675, 13887078],
    #[15899367, 10754144, 22340672, 16388396, 22168273, 29945930, 22995952, 11697111,
      813181, 1094366, 19942480, 23373824, 2389053, 7776266, 4431698, 16818186,
      20722743, 23114170, 24038797, 22441351, 4866927, 20759613, 3917197, 15291221],
    #[28644693, 14803425, 24400958, 14059821, 24915526, 31406786, 3472278, 27204680,
      21437996, 17035701, 19304206, 23975936, 24838674, 20033794, 6001672, 383234,
      20863760, 4901200, 22141504, 6845250, 21978650, 2269714, 2585152, 30109193],
    #[27689459, 25304927, 20414177, 32808656, 22609464, 13830533, 3997813, 15103538,
      18652891, 1164963, 2250744, 24823808, 25086010, 19182338, 4754930, 641794,
      1123128, 8378620, 24183748, 22456518, 21011912, 2517050, 3107780, 11829771],
    #[9474451, 26344850, 110209, 30502013, 4946069, 31239707, 17725144, 33179489,
      3397925, 2671965, 720902, 24909824, 5349284, 19030786, 4951871, 3742466,
      943270, 25155836, 22959194, 4796248, 6035611, 17432484, 3206234, 25949589],
    #[32544384, 27567747, 20803912, 8563154, 6145166, 29237813, 1334345, 12593642,
      21722332, 21183487, 17947138, 20215808, 519572, 2534150, 3248404, 16909062,
      8195730, 4810910, 5152268, 22961418, 20079744, 18959764, 19093004, 25443196],
    #[28317365, 29063750, 1010112, 15790781, 5476031, 16644068, 21064143, 30667168,
      24984897, 7453797, 19989258, 19032064, 3148929, 20867594, 17259056, 1876490,
      2358923, 8319601, 6178042, 5134064, 24137393, 17943681, 19635450, 32336345],
    #[31517013, 12310982, 8008323, 26002599, 18552919, 26670676, 3329392, 29459298,
      21607375, 7168238, 6213898, 22464512, 6732108, 17635590, 4880661, 3264774,
      4737098, 23981352, 7445858, 23157860, 6735961, 18381132, 20440418, 27853890],
    #[15290027, 10395499, 4583709, 11559316, 2604388, 27607289, 17353795, 29459298,
      8171778, 4490000, 23967687, 24524800, 23767071, 2641867, 22412939, 19040203,
      5705684, 6772859, 24289199, 24184932, 4431508, 3446815, 276399, 10934236],
    #[32797291, 9976040, 24776641, 10244991, 18480927, 26150511, 8134861, 32600807,
      7250690, 22108984, 5873798, 24659968, 22361283, 6069126, 24913994, 23892870,
      21768005, 5583918, 23726955, 4737261, 19756169, 2208963, 3433323, 27411785],
    #[14411253, 11033832, 24514290, 26190290, 20712882, 28759537, 23056896, 33031545,
      7250690, 21945510, 5642104, 21534720, 22672880, 21634950, 21319636, 4851590,
      21009014, 8177584, 4824518, 7191104, 975396, 1816048, 19342790, 28177079],
    #[15557277, 16393564, 7608170, 32897725, 21724322, 8674193, 17369092, 32860370,
      18004742, 22480530, 16920363, 23410688, 24220780, 21402811, 6924101, 4820155,
      5290199, 4968360, 22159231, 5272516, 3320617, 2864236, 4183935, 10075557]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part21 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false),
  (13, false), (12, false), (13, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part21.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_336 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8064 8088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_336 :
    generatedNinthLowerSpinSourceQReplayWord 7 336 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 0)
    8064 24 0 (prefix_sizes 0) slice_336
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_337 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8088 8112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_337 :
    generatedNinthLowerSpinSourceQReplayWord 7 337 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 1)
    8088 24 0 (prefix_sizes 1) slice_337
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_338 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8112 8136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_338 :
    generatedNinthLowerSpinSourceQReplayWord 7 338 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 2)
    8112 24 0 (prefix_sizes 2) slice_338
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_339 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8136 8160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_339 :
    generatedNinthLowerSpinSourceQReplayWord 7 339 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 3)
    8136 24 0 (prefix_sizes 3) slice_339
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_340 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8160 8184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_340 :
    generatedNinthLowerSpinSourceQReplayWord 7 340 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 4)
    8160 24 0 (prefix_sizes 4) slice_340
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_341 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8184 8208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_341 :
    generatedNinthLowerSpinSourceQReplayWord 7 341 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 5)
    8184 24 0 (prefix_sizes 5) slice_341
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_342 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8208 8232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_342 :
    generatedNinthLowerSpinSourceQReplayWord 7 342 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 6)
    8208 24 0 (prefix_sizes 6) slice_342
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_343 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8232 8256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_343 :
    generatedNinthLowerSpinSourceQReplayWord 7 343 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 7)
    8232 24 0 (prefix_sizes 7) slice_343
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_344 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8256 8280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_344 :
    generatedNinthLowerSpinSourceQReplayWord 7 344 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 8)
    8256 24 0 (prefix_sizes 8) slice_344
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_345 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8280 8304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_345 :
    generatedNinthLowerSpinSourceQReplayWord 7 345 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 9)
    8280 24 0 (prefix_sizes 9) slice_345
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_346 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8304 8328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_346 :
    generatedNinthLowerSpinSourceQReplayWord 7 346 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 10)
    8304 24 0 (prefix_sizes 10) slice_346
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_347 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8328 8352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_347 :
    generatedNinthLowerSpinSourceQReplayWord 7 347 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 11)
    8328 24 0 (prefix_sizes 11) slice_347
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_348 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8352 8376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_348 :
    generatedNinthLowerSpinSourceQReplayWord 7 348 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 12)
    8352 24 0 (prefix_sizes 12) slice_348
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_349 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8376 8400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_349 :
    generatedNinthLowerSpinSourceQReplayWord 7 349 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 13)
    8376 24 0 (prefix_sizes 13) slice_349
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_350 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8400 8424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_350 :
    generatedNinthLowerSpinSourceQReplayWord 7 350 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 14)
    8400 24 0 (prefix_sizes 14) slice_350
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_351 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8424 8448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_351 :
    generatedNinthLowerSpinSourceQReplayWord 7 351 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 15)
    8424 24 0 (prefix_sizes 15) slice_351
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_352 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8448 8472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_21_352 :
    generatedNinthLowerSpinSourceQReplayWord 7 352 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part21 16)
    8448 24 0 (prefix_sizes 16) slice_352
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 336 352 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part21 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_21 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨336 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part21.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part21
    336 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (336 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
