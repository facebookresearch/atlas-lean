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
def generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 : Fin 17 → Array ℕ :=
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
    #[27495407, 10693119, 20966106, 14024343, 2622749, 12605294, 3651588, 14757147,
      23659151, 4709197, 24885796, 7274496, 21741653, 17481820, 2996804, 21712988,
      16844809, 1157651, 18801178, 24441414, 3140113, 3493973, 4041242, 10372148],
    #[13788142, 29409790, 19786458, 13104790, 714013, 11622255, 7845892, 12791066,
      20515471, 7852877, 19577380, 7274496, 17418325, 573532, 25016900, 21583964,
      4259849, 21209619, 17621530, 23394886, 4057617, 24596565, 3123738, 31280181],
    #[27495407, 10693119, 20966106, 14024343, 2622749, 12605294, 3651588, 14757147,
      23659151, 4709197, 24885796, 7274496, 21741653, 17481820, 2996804, 21712988,
      16844809, 1157651, 18801178, 24441414, 3140113, 3493973, 4041242, 10372148],
    #[9155535, 9380319, 19116762, 32306871, 3251485, 16363342, 17741828, 13911355,
      24969871, 23780173, 21396004, 24053760, 4429909, 19830876, 2150980, 24053852,
      19728393, 104979, 19061274, 7115334, 2808337, 3997781, 16882202, 27739156],
    #[13954369, 13154418, 466801, 12044174, 3781986, 31068373, 17498624, 30202443,
      19089600, 19368070, 19375919, 17672192, 6823857, 7621054, 4185997, 2599358,
      22826511, 1274162, 8181565, 2436739, 4206652, 3880881, 4298557, 27542121],
    #[15466175, 16231308, 17686050, 28821390, 681903, 15316504, 3023053, 31677877,
      19220640, 1634168, 3298786, 19630080, 21118594, 22133523, 2490078, 17074963,
      6507921, 431007, 24122894, 20585757, 23072860, 18335362, 21710350, 28624393],
    #[8586382, 9553349, 23160947, 15452313, 20310449, 32119393, 21412931, 26070668,
      3688686, 3427271, 3772467, 22632448, 21584029, 22779958, 715043, 18466870,
      7870635, 24448511, 23948628, 19354978, 2601406, 19595421, 22240596, 12147541],
    #[26883952, 10003003, 8096032, 30981684, 20589135, 16394753, 7101808, 25697345,
      19360528, 17296650, 2334976, 23693312, 6076976, 24256424, 715043, 20357032,
      23240088, 24452511, 22480903, 17082287, 20218643, 1573424, 23672839, 9637478],
    #[26036423, 13041173, 5659939, 9310022, 24076428, 8420359, 22411727, 31718872,
      20345911, 6000472, 5818628, 22697984, 18006292, 22615984, 7299362, 17688496,
      4325028, 21141669, 18583041, 6224305, 18022454, 17041684, 18378241, 11722486],
    #[13225549, 14118510, 5248368, 28629973, 1621449, 15219283, 4709449, 9773601,
      5055055, 4802528, 4066052, 24676352, 24960831, 19376267, 18154541, 17098891,
      18112436, 19468257, 22812757, 921822, 3521298, 18786111, 20330581, 10382852]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters02Part05 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (5, true), (0, true), (3, false), (0, true),
  (0, false), (5, false), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters02Part05.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_080 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 1920 1944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_080 :
    generatedNinthLowerSpinSourceQReplayWord 2 80 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 0)
    1920 24 0 (prefix_sizes 0) slice_080
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (1920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_081 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 1944 1968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_081 :
    generatedNinthLowerSpinSourceQReplayWord 2 81 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 1)
    1944 24 0 (prefix_sizes 1) slice_081
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (1944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_082 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 1968 1992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_082 :
    generatedNinthLowerSpinSourceQReplayWord 2 82 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 2)
    1968 24 0 (prefix_sizes 2) slice_082
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (1968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_083 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 1992 2016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_083 :
    generatedNinthLowerSpinSourceQReplayWord 2 83 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 3)
    1992 24 0 (prefix_sizes 3) slice_083
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (1992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_084 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2016 2040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_084 :
    generatedNinthLowerSpinSourceQReplayWord 2 84 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 4)
    2016 24 0 (prefix_sizes 4) slice_084
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_085 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2040 2064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_085 :
    generatedNinthLowerSpinSourceQReplayWord 2 85 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 5)
    2040 24 0 (prefix_sizes 5) slice_085
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_086 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2064 2088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_086 :
    generatedNinthLowerSpinSourceQReplayWord 2 86 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 6)
    2064 24 0 (prefix_sizes 6) slice_086
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_087 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2088 2112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_087 :
    generatedNinthLowerSpinSourceQReplayWord 2 87 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 7)
    2088 24 0 (prefix_sizes 7) slice_087
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_088 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2112 2136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_088 :
    generatedNinthLowerSpinSourceQReplayWord 2 88 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 8)
    2112 24 0 (prefix_sizes 8) slice_088
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_089 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2136 2160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_089 :
    generatedNinthLowerSpinSourceQReplayWord 2 89 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 9)
    2136 24 0 (prefix_sizes 9) slice_089
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_090 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2160 2184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_090 :
    generatedNinthLowerSpinSourceQReplayWord 2 90 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 10)
    2160 24 0 (prefix_sizes 10) slice_090
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_091 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2184 2208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_091 :
    generatedNinthLowerSpinSourceQReplayWord 2 91 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 11)
    2184 24 0 (prefix_sizes 11) slice_091
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_092 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2208 2232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_092 :
    generatedNinthLowerSpinSourceQReplayWord 2 92 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 12)
    2208 24 0 (prefix_sizes 12) slice_092
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_093 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2232 2256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_093 :
    generatedNinthLowerSpinSourceQReplayWord 2 93 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 13)
    2232 24 0 (prefix_sizes 13) slice_093
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_094 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2256 2280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_094 :
    generatedNinthLowerSpinSourceQReplayWord 2 94 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 14)
    2256 24 0 (prefix_sizes 14) slice_094
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_095 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2280 2304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_095 :
    generatedNinthLowerSpinSourceQReplayWord 2 95 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 15)
    2280 24 0 (prefix_sizes 15) slice_095
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_05_096 :
    generatedNinthLowerSpinSourceQReplayWord 2 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part05 16)
    2304 24 0 (prefix_sizes 16) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords02.extract 80 96 =
      generatedNinthLowerSpinLiteralQReplayLetters02Part05 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_02_part_05 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 2 ⟨80 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters02Part05.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords02
    generatedNinthLowerSpinLiteralQReplayLetters02Part05
    80 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords02.getD (80 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
