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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 : Fin 17 → Array ℕ :=
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
    #[29834231, 32913895, 24109786, 27446927, 20034845, 31520630, 23705604, 16391427,
      19450511, 22313805, 17820196, 24053760, 5900373, 24053852, 5233220, 19830876,
      24446985, 524819, 7555610, 8165958, 6046225, 2396245, 5245466, 32326700],
    #[11853405, 33401710, 4058993, 26092690, 24223074, 9458633, 21148160, 12732759,
      16982208, 24545414, 19945263, 17672192, 7507889, 2599358, 3307405, 7621054,
      18169359, 4495666, 23217981, 6837891, 5703740, 2205617, 23004989, 9668981],
    #[27590237, 14371694, 17894946, 11663212, 24289199, 26932986, 5718221, 12729687,
      18153632, 4796280, 3507682, 19630080, 24030850, 17074963, 947934, 22133523,
      1764753, 7441311, 8300046, 23172381, 23529564, 20665986, 4584974, 12377835],
    #[15124971, 10061984, 17696883, 25765372, 5837233, 16115460, 20560963, 9724905,
      4878574, 5782471, 6131763, 22632448, 22284445, 18466870, 5484835, 22779958,
      2562219, 24892927, 3980628, 20241762, 6535614, 20336797, 167252, 14192176],
    #[30436747, 11110592, 264480, 10867919, 5243471, 32284922, 2329968, 28899002,
      22250256, 21855498, 4288768, 23693312, 5757488, 20357032, 6512931, 24256424,
      19758488, 22803871, 3540999, 18952111, 22440723, 1270320, 538631, 13335709],
    #[29830814, 29005900, 5143843, 12749087, 2615436, 15034974, 20314575, 16681857,
      22584375, 5144408, 3565828, 22697984, 23331092, 17688496, 3488034, 22615984,
      6540964, 19271845, 6110721, 5026225, 20944950, 24299796, 6217217, 29290671],
    #[29447590, 14300549, 1135984, 14377022, 21251529, 9949624, 4226121, 13949386,
      6928975, 7014368, 6449924, 24676352, 18419519, 17098891, 23956525, 19376267,
      22204340, 20596705, 641109, 7899358, 2679570, 24868671, 6547541, 10558959],
    #[9340598, 12113552, 22426063, 13721618, 16870165, 33234641, 17245912, 9886534,
      3334284, 7235637, 19165708, 22427648, 4866371, 22610888, 20016250, 23348168,
      1145483, 7525690, 6156209, 5497977, 21929273, 3422531, 1404849, 11334716],
    #[27448293, 11269213, 5251535, 13517804, 728646, 33234641, 1335413, 26656550,
      18088076, 7065336, 18981057, 22476800, 4882755, 7771222, 4119428, 5096534,
      17313045, 23561111, 22146690, 4235988, 21494471, 1313091, 18460290, 27931740],
    #[16354152, 15444195, 23118921, 16133479, 1356497, 28066850, 4627350, 10976119,
      2403785, 20766218, 3427651, 23091200, 2075008, 5058530, 4071109, 7544802,
      22441570, 4421375, 19675293, 180095, 3778373, 74112, 22071453, 10651116]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part05 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (5, true), (0, true), (4, false), (12, true),
  (13, true), (12, true), (13, true), (12, true),
  (12, true), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part05.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_080 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1920 1944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_080 :
    generatedNinthLowerSpinSourceQReplayWord 5 80 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 0)
    1920 24 0 (prefix_sizes 0) slice_080
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_081 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1944 1968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_081 :
    generatedNinthLowerSpinSourceQReplayWord 5 81 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 1)
    1944 24 0 (prefix_sizes 1) slice_081
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_082 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1968 1992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_082 :
    generatedNinthLowerSpinSourceQReplayWord 5 82 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 2)
    1968 24 0 (prefix_sizes 2) slice_082
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_083 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1992 2016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_083 :
    generatedNinthLowerSpinSourceQReplayWord 5 83 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 3)
    1992 24 0 (prefix_sizes 3) slice_083
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_084 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2016 2040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_084 :
    generatedNinthLowerSpinSourceQReplayWord 5 84 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 4)
    2016 24 0 (prefix_sizes 4) slice_084
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_085 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2040 2064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_085 :
    generatedNinthLowerSpinSourceQReplayWord 5 85 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 5)
    2040 24 0 (prefix_sizes 5) slice_085
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_086 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2064 2088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_086 :
    generatedNinthLowerSpinSourceQReplayWord 5 86 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 6)
    2064 24 0 (prefix_sizes 6) slice_086
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_087 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2088 2112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_087 :
    generatedNinthLowerSpinSourceQReplayWord 5 87 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 7)
    2088 24 0 (prefix_sizes 7) slice_087
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_088 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2112 2136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_088 :
    generatedNinthLowerSpinSourceQReplayWord 5 88 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 8)
    2112 24 0 (prefix_sizes 8) slice_088
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_089 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2136 2160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_089 :
    generatedNinthLowerSpinSourceQReplayWord 5 89 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 9)
    2136 24 0 (prefix_sizes 9) slice_089
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_090 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2160 2184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_090 :
    generatedNinthLowerSpinSourceQReplayWord 5 90 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 10)
    2160 24 0 (prefix_sizes 10) slice_090
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_091 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2184 2208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_091 :
    generatedNinthLowerSpinSourceQReplayWord 5 91 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 11)
    2184 24 0 (prefix_sizes 11) slice_091
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_092 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2208 2232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_092 :
    generatedNinthLowerSpinSourceQReplayWord 5 92 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 12)
    2208 24 0 (prefix_sizes 12) slice_092
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_093 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2232 2256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_093 :
    generatedNinthLowerSpinSourceQReplayWord 5 93 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 13)
    2232 24 0 (prefix_sizes 13) slice_093
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_094 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2256 2280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_094 :
    generatedNinthLowerSpinSourceQReplayWord 5 94 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 14)
    2256 24 0 (prefix_sizes 14) slice_094
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_095 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2280 2304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_095 :
    generatedNinthLowerSpinSourceQReplayWord 5 95 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 15)
    2280 24 0 (prefix_sizes 15) slice_095
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_05_096 :
    generatedNinthLowerSpinSourceQReplayWord 5 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part05 16)
    2304 24 0 (prefix_sizes 16) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 80 96 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part05 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_05 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨80 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part05.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part05
    80 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (80 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
