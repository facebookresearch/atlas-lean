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
def generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 : Fin 17 → Array ℕ :=
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
    #[12592101, 30573045, 20966106, 15007389, 7578909, 8413028, 3651588, 28978449,
      4457103, 4184909, 5093924, 7274496, 23513173, 6799452, 18004548, 19290204,
      4259849, 21209619, 17621530, 17562182, 4057617, 18370645, 3123738, 16403518],
    #[28429284, 11626996, 19786458, 16184988, 5326109, 15818597, 7845892, 26750224,
      1313423, 1037133, 1882660, 7274496, 19185749, 23445596, 4373060, 19157084,
      16844809, 1157651, 18801178, 18608710, 3140113, 5918805, 4041242, 28918847],
    #[12592101, 30573045, 20966106, 15007389, 7578909, 8413028, 3651588, 28978449,
      4457103, 4184909, 5093924, 7274496, 23513173, 6799452, 18004548, 19290204,
      4259849, 21209619, 17621530, 17562182, 4057617, 18370645, 3123738, 16403518],
    #[13636549, 29788629, 19116762, 31848125, 23737629, 8496964, 17741828, 12012849,
      5243535, 18013005, 24146468, 24053760, 7245909, 4429916, 2087492, 16908380,
      7143433, 5478931, 3199514, 18059846, 20501009, 17825877, 1282586, 33246238],
    #[31426383, 13482620, 466801, 31591808, 23207266, 25432795, 17498624, 26851397,
      3008704, 19482758, 19033903, 17672192, 6731697, 20642238, 4134797, 6885822,
      1857039, 6095154, 24297277, 23461507, 21911612, 20289457, 22019901, 32628839],
    #[33203586, 13150385, 17686050, 13167795, 22486959, 29062437, 3023053, 28102280,
      776352, 397176, 105954, 19630080, 23897730, 1043219, 2438878, 22729491,
      18056593, 5768095, 6180366, 4857117, 5130332, 3757698, 6626830, 16487732],
    #[32862353, 26868186, 23160947, 15453318, 4936113, 25990782, 21412931, 10338963,
      23464174, 5901255, 1136691, 22632448, 18288797, 7276598, 2810147, 19746870,
      18006187, 23174655, 1254740, 7177570, 22673854, 7684253, 2954580, 25777994],
    #[29782588, 28995447, 8096032, 32656248, 6578767, 25593677, 7101808, 10666253,
      5888784, 24726794, 747776, 23693312, 2228784, 4235176, 708899, 17045416,
      3057048, 21474719, 2719751, 4761519, 4852499, 23507504, 1552391, 12182314],
    #[15886356, 31516358, 5659939, 11419541, 5367948, 13681876, 22411727, 9168139,
      2978871, 4890456, 8085764, 22697984, 17418516, 4732848, 2971938, 18665392,
      21747364, 17926309, 4371969, 18278833, 4864054, 2033940, 4281857, 26801701],
    #[30203451, 9971224, 5248368, 12368803, 16881097, 15888933, 4709449, 13724247,
      21381711, 5191648, 7037700, 24676352, 24622911, 6547595, 22297645, 21012619,
      5994420, 19693537, 1458261, 16777438, 25158418, 1427263, 8151125, 26941042]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters00Part05 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (5, true), (0, true), (1, false), (0, true),
  (0, false), (5, false), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters00Part05.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_080 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1920 1944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_080 :
    generatedNinthLowerSpinSourceQReplayWord 0 80 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 0)
    1920 24 0 (prefix_sizes 0) slice_080
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_081 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1944 1968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_081 :
    generatedNinthLowerSpinSourceQReplayWord 0 81 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 1)
    1944 24 0 (prefix_sizes 1) slice_081
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_082 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1968 1992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_082 :
    generatedNinthLowerSpinSourceQReplayWord 0 82 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 2)
    1968 24 0 (prefix_sizes 2) slice_082
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_083 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1992 2016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_083 :
    generatedNinthLowerSpinSourceQReplayWord 0 83 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 3)
    1992 24 0 (prefix_sizes 3) slice_083
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_084 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2016 2040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_084 :
    generatedNinthLowerSpinSourceQReplayWord 0 84 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 4)
    2016 24 0 (prefix_sizes 4) slice_084
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_085 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2040 2064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_085 :
    generatedNinthLowerSpinSourceQReplayWord 0 85 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 5)
    2040 24 0 (prefix_sizes 5) slice_085
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_086 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2064 2088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_086 :
    generatedNinthLowerSpinSourceQReplayWord 0 86 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 6)
    2064 24 0 (prefix_sizes 6) slice_086
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_087 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2088 2112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_087 :
    generatedNinthLowerSpinSourceQReplayWord 0 87 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 7)
    2088 24 0 (prefix_sizes 7) slice_087
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_088 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2112 2136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_088 :
    generatedNinthLowerSpinSourceQReplayWord 0 88 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 8)
    2112 24 0 (prefix_sizes 8) slice_088
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_089 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2136 2160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_089 :
    generatedNinthLowerSpinSourceQReplayWord 0 89 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 9)
    2136 24 0 (prefix_sizes 9) slice_089
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_090 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2160 2184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_090 :
    generatedNinthLowerSpinSourceQReplayWord 0 90 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 10)
    2160 24 0 (prefix_sizes 10) slice_090
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_091 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2184 2208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_091 :
    generatedNinthLowerSpinSourceQReplayWord 0 91 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 11)
    2184 24 0 (prefix_sizes 11) slice_091
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_092 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2208 2232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_092 :
    generatedNinthLowerSpinSourceQReplayWord 0 92 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 12)
    2208 24 0 (prefix_sizes 12) slice_092
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_093 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2232 2256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_093 :
    generatedNinthLowerSpinSourceQReplayWord 0 93 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 13)
    2232 24 0 (prefix_sizes 13) slice_093
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_094 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2256 2280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_094 :
    generatedNinthLowerSpinSourceQReplayWord 0 94 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 14)
    2256 24 0 (prefix_sizes 14) slice_094
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_095 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2280 2304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_095 :
    generatedNinthLowerSpinSourceQReplayWord 0 95 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 15)
    2280 24 0 (prefix_sizes 15) slice_095
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_05_096 :
    generatedNinthLowerSpinSourceQReplayWord 0 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part05 16)
    2304 24 0 (prefix_sizes 16) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords00.extract 80 96 =
      generatedNinthLowerSpinLiteralQReplayLetters00Part05 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_00_part_05 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 0 ⟨80 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters00Part05.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords00
    generatedNinthLowerSpinLiteralQReplayLetters00Part05
    80 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords00.getD (80 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
