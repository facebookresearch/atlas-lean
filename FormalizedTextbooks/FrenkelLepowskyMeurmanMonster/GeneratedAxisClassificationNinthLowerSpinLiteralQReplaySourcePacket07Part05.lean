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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 : Fin 17 → Array ℕ :=
  ![
    #[26886888, 12412835, 7123232, 28965804, 3228239, 26785689, 7101808, 10838489,
      5888784, 7953674, 17156352, 23693312, 20263472, 1808296, 715043, 6231976,
      23240088, 1873311, 4096007, 17082287, 6097683, 24218160, 45063, 11588606],
    #[12522533, 27153774, 23490675, 10881074, 2666929, 26346186, 21412931, 11195943,
      23464174, 23727047, 20957235, 22632448, 1048733, 180278, 715043, 4231222,
      7870635, 2905599, 3421524, 19354978, 25094590, 7493789, 656724, 28365822],
    #[26192686, 29933085, 17352226, 14541343, 19333039, 25885577, 3023053, 33140772,
      776352, 20348792, 23100898, 19630080, 6928002, 8008467, 2490078, 3080979,
      6507921, 19733407, 6004238, 20585757, 4954204, 3952258, 6344206, 30395288],
    #[10459982, 30310013, 268145, 31646081, 19082594, 25583322, 17498624, 31056964,
      3008704, 2697350, 6520623, 17672192, 23443377, 24764862, 4185997, 19530174,
      22826511, 18798898, 24215357, 2436739, 21862460, 20357041, 21774141, 32533606],
    #[13640646, 33272278, 23182042, 31061694, 19399965, 30713671, 17741828, 10571058,
      5243535, 4709197, 7434788, 24053760, 19697749, 4296796, 2150980, 92,
      19728393, 24023571, 5100058, 7115334, 21352977, 22153301, 7246362, 30624797],
    #[13898726, 33274358, 8252122, 13434526, 20028701, 29450087, 3651588, 12068114,
      4457103, 23780173, 21805604, 7274496, 19185749, 23445596, 2996804, 19157084,
      16844809, 8301075, 24240666, 24441414, 4254225, 5918805, 5417498, 12995645],
    #[15072231, 30953975, 7334618, 10419871, 1275165, 32528230, 7845892, 14298387,
      1313423, 22729549, 18725412, 7274496, 23513173, 6799452, 25016900, 19290204,
      4259849, 19702291, 23323162, 23394886, 5433873, 18370645, 4237850, 29707324],
    #[9810534, 29630293, 20834161, 13310121, 5586274, 29900786, 4510208, 12715372,
      2220224, 19742854, 21813039, 892928, 22040497, 21213630, 21723021, 1071550,
      5498383, 23062834, 4190013, 22144643, 835644, 17000369, 16951101, 9825614],
    #[9434965, 32021094, 1115682, 32005732, 6307759, 29900786, 22094029, 15213663,
      114848, 2369400, 6288866, 2850816, 8023682, 5657363, 24622814, 17001235,
      22869393, 22870943, 18206222, 5776669, 17432668, 3118722, 3053070, 28368867],
    #[26219503, 30157476, 917619, 31911928, 21471665, 32304384, 420931, 11123181,
      23793902, 1475527, 6811699, 5853184, 7694493, 8233014, 20734243, 20969526,
      23204011, 5223935, 21878100, 2219362, 2949566, 1519773, 7597396, 11009076],
    #[9818434, 15297545, 17039648, 15292422, 21934671, 30813235, 18636144, 9480819,
      7529232, 18031882, 5050624, 6914048, 24558128, 6567848, 18632995, 18923432,
      6206872, 4830623, 22511623, 1183663, 17314579, 20054576, 6928391, 8874068],
    #[32031887, 15374941, 21919011, 11162382, 20662412, 29909071, 2042319, 16249232,
      7269431, 8054616, 964868, 5918720, 5402900, 5459888, 20437282, 17282992,
      17503908, 5275813, 21198337, 17584561, 17498166, 4503828, 4234753, 25477822],
    #[30299546, 33410489, 17915248, 9981954, 1172937, 11788676, 19586121, 12683766,
      22461007, 8339424, 436996, 7897088, 2494271, 5390475, 4635693, 24184971,
      3893172, 2979809, 24596565, 22067422, 3988242, 4486975, 1931349, 12875219],
    #[11437994, 16338828, 5650895, 33243406, 1170197, 9998285, 1529560, 9325146,
      20062348, 2961461, 22004236, 5648384, 21659971, 4963272, 7535738, 24572872,
      16974475, 20153658, 17745841, 17986681, 17679673, 20248899, 4607921, 12356896],
    #[26088394, 29777010, 22030799, 30311363, 17534534, 25345790, 18100341, 25358089,
      1360012, 4089592, 21807297, 5697536, 21643587, 23215190, 23837572, 5858390,
      1852693, 2495383, 267906, 16904916, 17978055, 18139459, 21782146, 25599091],
    #[12311118, 26747333, 6343753, 33279041, 21385937, 31368452, 20216726, 16325201,
      17083849, 19686922, 4861251, 6311936, 20949376, 22845410, 17739461, 6467554,
      6805090, 17864447, 5136541, 24207231, 2694981, 18948480, 20093085, 30411978],
    #[30322051, 27188807, 22697688, 25247192, 18704496, 25941846, 398320, 30035129,
      19485461, 530260, 3122642, 7684096, 18382285, 5392699, 299545, 22126907,
      7212278, 18481163, 3403005, 7658950, 18847700, 21423565, 18023677, 14525968]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part05 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (5, true), (0, true), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part05.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_080 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 1920 1944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_080 :
    generatedNinthLowerSpinSourceQReplayWord 7 80 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 0)
    1920 24 0 (prefix_sizes 0) slice_080
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (1920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_081 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 1944 1968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_081 :
    generatedNinthLowerSpinSourceQReplayWord 7 81 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 1)
    1944 24 0 (prefix_sizes 1) slice_081
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (1944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_082 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 1968 1992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_082 :
    generatedNinthLowerSpinSourceQReplayWord 7 82 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 2)
    1968 24 0 (prefix_sizes 2) slice_082
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (1968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_083 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 1992 2016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_083 :
    generatedNinthLowerSpinSourceQReplayWord 7 83 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 3)
    1992 24 0 (prefix_sizes 3) slice_083
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (1992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_084 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2016 2040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_084 :
    generatedNinthLowerSpinSourceQReplayWord 7 84 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 4)
    2016 24 0 (prefix_sizes 4) slice_084
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_085 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2040 2064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_085 :
    generatedNinthLowerSpinSourceQReplayWord 7 85 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 5)
    2040 24 0 (prefix_sizes 5) slice_085
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_086 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2064 2088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_086 :
    generatedNinthLowerSpinSourceQReplayWord 7 86 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 6)
    2064 24 0 (prefix_sizes 6) slice_086
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_087 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2088 2112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_087 :
    generatedNinthLowerSpinSourceQReplayWord 7 87 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 7)
    2088 24 0 (prefix_sizes 7) slice_087
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_088 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2112 2136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_088 :
    generatedNinthLowerSpinSourceQReplayWord 7 88 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 8)
    2112 24 0 (prefix_sizes 8) slice_088
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_089 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2136 2160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_089 :
    generatedNinthLowerSpinSourceQReplayWord 7 89 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 9)
    2136 24 0 (prefix_sizes 9) slice_089
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_090 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2160 2184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_090 :
    generatedNinthLowerSpinSourceQReplayWord 7 90 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 10)
    2160 24 0 (prefix_sizes 10) slice_090
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_091 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2184 2208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_091 :
    generatedNinthLowerSpinSourceQReplayWord 7 91 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 11)
    2184 24 0 (prefix_sizes 11) slice_091
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_092 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2208 2232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_092 :
    generatedNinthLowerSpinSourceQReplayWord 7 92 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 12)
    2208 24 0 (prefix_sizes 12) slice_092
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_093 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2232 2256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_093 :
    generatedNinthLowerSpinSourceQReplayWord 7 93 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 13)
    2232 24 0 (prefix_sizes 13) slice_093
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_094 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2256 2280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_094 :
    generatedNinthLowerSpinSourceQReplayWord 7 94 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 14)
    2256 24 0 (prefix_sizes 14) slice_094
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_095 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2280 2304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_095 :
    generatedNinthLowerSpinSourceQReplayWord 7 95 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 15)
    2280 24 0 (prefix_sizes 15) slice_095
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_05_096 :
    generatedNinthLowerSpinSourceQReplayWord 7 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part05 16)
    2304 24 0 (prefix_sizes 16) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 80 96 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part05 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_05 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨80 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part05.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part05
    80 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (80 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
