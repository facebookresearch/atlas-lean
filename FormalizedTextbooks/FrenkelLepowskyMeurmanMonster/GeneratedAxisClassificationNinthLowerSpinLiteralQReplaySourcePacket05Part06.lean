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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 : Fin 17 → Array ℕ :=
  ![
    #[16354152, 15444195, 23118921, 16133479, 1356497, 28066850, 4627350, 10976119,
      2403785, 20766218, 3427651, 23091200, 2075008, 5058530, 4071109, 7544802,
      22441570, 4421375, 19675293, 180095, 3778373, 74112, 22071453, 10651116],
    #[13493166, 33314922, 5922520, 30581749, 3881072, 26777979, 23589872, 13517460,
      7267093, 6270804, 2012626, 24463360, 6278605, 21291323, 18125337, 21430587,
      20911350, 8208395, 17151229, 22293958, 21508052, 87501, 19223805, 33435709],
    #[33240014, 31793044, 22005877, 15603366, 1906800, 11468059, 4718606, 13448281,
      23352902, 21031114, 20797311, 22259712, 4603443, 24397115, 18101881, 23172411,
      19948296, 7464280, 20362832, 7449451, 22505546, 542259, 19285584, 33284848],
    #[13493166, 33314922, 5922520, 30581749, 3881072, 26777979, 23589872, 13517460,
      7267093, 6270804, 2012626, 24463360, 6278605, 21291323, 18125337, 21430587,
      20911350, 8208395, 17151229, 22293958, 21508052, 87501, 19223805, 33435709],
    #[16354152, 15444195, 23118921, 16133479, 1356497, 28066850, 4627350, 10976119,
      2403785, 20766218, 3427651, 23091200, 2075008, 5058530, 4071109, 7544802,
      22441570, 4421375, 19675293, 180095, 3778373, 74112, 22071453, 10651116],
    #[27448293, 11269213, 5251535, 13517804, 728646, 33234641, 1335413, 26656550,
      18088076, 7065336, 18981057, 22476800, 4882755, 7771222, 4119428, 5096534,
      17313045, 23561111, 22146690, 4235988, 21494471, 1313091, 18460290, 27931740],
    #[9340598, 12113552, 22426063, 13721618, 16870165, 33234641, 17245912, 9886534,
      3334284, 7235637, 19165708, 22427648, 4866371, 22610888, 20016250, 23348168,
      1145483, 7525690, 6156209, 5497977, 21929273, 3422531, 1404849, 11334716],
    #[29447590, 14300549, 1135984, 14377022, 21251529, 9949624, 4226121, 13949386,
      6928975, 7014368, 6449924, 24676352, 18419519, 17098891, 23956525, 19376267,
      22204340, 20596705, 641109, 7899358, 2679570, 24868671, 6547541, 10558959],
    #[29830814, 29005900, 5143843, 12749087, 2615436, 15034974, 20314575, 16681857,
      22584375, 5144408, 3565828, 22697984, 23331092, 17688496, 3488034, 22615984,
      6540964, 19271845, 6110721, 5026225, 20944950, 24299796, 6217217, 29290671],
    #[30142381, 12343340, 7912739, 13810047, 19343500, 33524493, 1378767, 31763154,
      24299780, 6416582, 707639, 23894016, 21910567, 1360942, 3210127, 5686318,
      7772169, 20141672, 24976993, 22254159, 1101736, 24685607, 23645793, 25440668],
    #[15519935, 32847143, 3446128, 13901980, 6571465, 11535363, 23460937, 13831281,
      25082628, 22303554, 22358607, 22890496, 921204, 288891, 4577732, 485499,
      4578831, 2574072, 17193207, 24578188, 3651504, 6944372, 23869687, 25778422],
    #[27427284, 13989744, 20742607, 8618482, 4643605, 25356371, 1402584, 11050436,
      4919820, 1871239, 23249036, 20744192, 3388355, 127896, 20609864, 258968,
      6461531, 19674634, 19209809, 2164169, 8112267, 1588163, 18181713, 28177246],
    #[9970823, 15512718, 2908623, 27681599, 23879238, 12515680, 18874485, 28579991,
      6168769, 20716007, 4513932, 19576832, 16818446, 17728614, 19082454, 18527334,
      25038184, 2528057, 20315729, 1618487, 24604120, 17631502, 20291153, 9159486],
    #[26640026, 9484437, 22733897, 32529681, 19264209, 8688038, 19962774, 29290227,
      19688771, 22563694, 21097929, 22706176, 1534218, 4456446, 22170411, 45054,
      5664500, 4748831, 6322411, 21380885, 7107105, 5153034, 5286123, 29757470],
    #[10821542, 26185725, 2080472, 26371170, 17307760, 29573860, 2237424, 27703563,
      23066066, 20011168, 18658069, 19965952, 24042250, 11264, 4944682, 3202048,
      5234442, 4103264, 4215658, 5248874, 1439776, 21410570, 6325098, 31460405],
    #[28527558, 10862254, 19712117, 10205084, 17307760, 29762601, 17498126, 11595115,
      5031807, 20007104, 2147910, 19965952, 7253770, 1051648, 21825354, 3202048,
      25148170, 4103264, 23074666, 20988778, 3393600, 7788298, 22079338, 29727480],
    #[10821542, 26185725, 2080472, 26371170, 17307760, 29573860, 2237424, 27703563,
      23066066, 20011168, 18658069, 19965952, 24042250, 11264, 4944682, 3202048,
      5234442, 4103264, 4215658, 5248874, 1439776, 21410570, 6325098, 31460405]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part06 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (13, false), (12, true), (12, true), (13, true),
  (12, true), (12, true), (13, true), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part06.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_096 :
    generatedNinthLowerSpinSourceQReplayWord 5 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 0)
    2304 24 0 (prefix_sizes 0) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_097 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2328 2352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_097 :
    generatedNinthLowerSpinSourceQReplayWord 5 97 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 1)
    2328 24 0 (prefix_sizes 1) slice_097
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_098 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2352 2376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_098 :
    generatedNinthLowerSpinSourceQReplayWord 5 98 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 2)
    2352 24 0 (prefix_sizes 2) slice_098
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_099 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2376 2400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_099 :
    generatedNinthLowerSpinSourceQReplayWord 5 99 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 3)
    2376 24 0 (prefix_sizes 3) slice_099
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_100 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2400 2424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_100 :
    generatedNinthLowerSpinSourceQReplayWord 5 100 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 4)
    2400 24 0 (prefix_sizes 4) slice_100
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_101 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2424 2448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_101 :
    generatedNinthLowerSpinSourceQReplayWord 5 101 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 5)
    2424 24 0 (prefix_sizes 5) slice_101
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_102 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2448 2472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_102 :
    generatedNinthLowerSpinSourceQReplayWord 5 102 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 6)
    2448 24 0 (prefix_sizes 6) slice_102
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_103 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2472 2496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_103 :
    generatedNinthLowerSpinSourceQReplayWord 5 103 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 7)
    2472 24 0 (prefix_sizes 7) slice_103
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_104 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2496 2520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_104 :
    generatedNinthLowerSpinSourceQReplayWord 5 104 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 8)
    2496 24 0 (prefix_sizes 8) slice_104
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_105 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2520 2544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_105 :
    generatedNinthLowerSpinSourceQReplayWord 5 105 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 9)
    2520 24 0 (prefix_sizes 9) slice_105
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_106 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2544 2568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_106 :
    generatedNinthLowerSpinSourceQReplayWord 5 106 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 10)
    2544 24 0 (prefix_sizes 10) slice_106
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_107 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2568 2592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_107 :
    generatedNinthLowerSpinSourceQReplayWord 5 107 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 11)
    2568 24 0 (prefix_sizes 11) slice_107
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_108 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2592 2616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_108 :
    generatedNinthLowerSpinSourceQReplayWord 5 108 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 12)
    2592 24 0 (prefix_sizes 12) slice_108
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_109 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2616 2640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_109 :
    generatedNinthLowerSpinSourceQReplayWord 5 109 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 13)
    2616 24 0 (prefix_sizes 13) slice_109
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_110 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2640 2664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_110 :
    generatedNinthLowerSpinSourceQReplayWord 5 110 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 14)
    2640 24 0 (prefix_sizes 14) slice_110
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_111 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2664 2688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_111 :
    generatedNinthLowerSpinSourceQReplayWord 5 111 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 15)
    2664 24 0 (prefix_sizes 15) slice_111
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_06_112 :
    generatedNinthLowerSpinSourceQReplayWord 5 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part06 16)
    2688 24 0 (prefix_sizes 16) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 96 112 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part06 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_06 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨96 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part06.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part06
    96 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (96 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
