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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 : Fin 17 → Array ℕ :=
  ![
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
    #[32358533, 10712218, 7476256, 33371785, 19264209, 29485102, 5115918, 29708524,
      1223380, 21934735, 2057784, 22706176, 5095156, 3178494, 5928244, 45054,
      3397898, 4748831, 7753493, 24078571, 7502784, 2823924, 3481365, 32541078],
    #[15978430, 14804099, 5594591, 29369156, 23879238, 32178735, 17240078, 14676910,
      23081143, 8105656, 23456999, 19576832, 19967336, 18535526, 22845423, 18527334,
      19755278, 2528057, 24302135, 3993169, 5241479, 22967656, 23519799, 10446961],
    #[30752734, 31143376, 21331423, 13583578, 4643605, 29635025, 1586160, 31400910,
      8025476, 21891093, 21608884, 20744192, 837723, 3376024, 25146690, 258968,
      1602499, 19674634, 23954889, 2887249, 7773465, 6475867, 24085961, 11188956],
    #[13058087, 8462625, 24593440, 31973931, 18408248, 30324860, 21074012, 15679566,
      359327, 24912692, 17262545, 22689792, 5963711, 2108414, 22196445, 1059838,
      3230785, 8058708, 23321365, 21641451, 23949154, 1857471, 18926357, 14158975],
    #[25893414, 9025580, 5449845, 16454190, 1792784, 10409369, 7987646, 14310539,
      18818559, 22080016, 7546150, 21518336, 24096138, 1001554, 5455992, 362578,
      3411416, 22359776, 5395256, 24646506, 25062898, 19948938, 1725240, 14982602],
    #[27178529, 26924327, 3171222, 28226849, 7767095, 33110955, 19891679, 9418650,
      16777223, 23588147, 5409407, 24569856, 6620049, 5433776, 559001, 7727536,
      18788897, 6961457, 21400336, 22993568, 20345864, 4352913, 21138192, 12861204],
    #[28857889, 27947303, 16779158, 12011231, 6082820, 15514982, 615903, 29299610,
      17478996, 24190259, 23955937, 23463936, 21570242, 5777635, 3285706, 8333539,
      20468257, 5581519, 7952622, 22874125, 20316168, 22960834, 5994734, 32336106],
    #[29157926, 13832146, 3579787, 8780214, 6600960, 9907217, 21893566, 8448885,
      17161742, 22575632, 2934623, 17094656, 1601925, 5203037, 7789449, 4564061,
      261592, 18625912, 19155104, 677117, 19184140, 7920005, 23378080, 12632492],
    #[9310247, 31731015, 19150918, 26604112, 6424588, 12149555, 573532, 25840680,
      24737780, 22414132, 24875253, 24647680, 23048114, 23866355, 5098678, 22817779,
      7871553, 4306735, 24046446, 5638301, 6120196, 24803250, 22207342, 30347362],
    #[30281694, 14358989, 23343554, 28702964, 24959744, 29285866, 16974832, 14618579,
      24581476, 16971797, 17327471, 24934400, 23860390, 21524325, 19207586, 24649573,
      213955, 5093924, 19753447, 7188098, 4356, 22400166, 18168295, 30419695],
    #[16699326, 13949491, 21037935, 26438900, 7670014, 9272103, 659470, 15387934,
      7028823, 1162936, 19830031, 21673984, 21336888, 23259702, 3208975, 23235126,
      18903310, 24697993, 916871, 24616881, 3978295, 21781304, 3517831, 33102193]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part08 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (12, false), (12, false), (13, false),
  (12, true), (12, true), (12, true), (13, false),
  (12, false), (12, false), (12, false), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part08.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_128 :
    generatedNinthLowerSpinSourceQReplayWord 5 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 0)
    3072 24 0 (prefix_sizes 0) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_129 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3096 3120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_129 :
    generatedNinthLowerSpinSourceQReplayWord 5 129 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 1)
    3096 24 0 (prefix_sizes 1) slice_129
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_130 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3120 3144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_130 :
    generatedNinthLowerSpinSourceQReplayWord 5 130 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 2)
    3120 24 0 (prefix_sizes 2) slice_130
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_131 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3144 3168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_131 :
    generatedNinthLowerSpinSourceQReplayWord 5 131 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 3)
    3144 24 0 (prefix_sizes 3) slice_131
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_132 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3168 3192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_132 :
    generatedNinthLowerSpinSourceQReplayWord 5 132 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 4)
    3168 24 0 (prefix_sizes 4) slice_132
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_133 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3192 3216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_133 :
    generatedNinthLowerSpinSourceQReplayWord 5 133 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 5)
    3192 24 0 (prefix_sizes 5) slice_133
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_134 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3216 3240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_134 :
    generatedNinthLowerSpinSourceQReplayWord 5 134 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 6)
    3216 24 0 (prefix_sizes 6) slice_134
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_135 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3240 3264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_135 :
    generatedNinthLowerSpinSourceQReplayWord 5 135 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 7)
    3240 24 0 (prefix_sizes 7) slice_135
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_136 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3264 3288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_136 :
    generatedNinthLowerSpinSourceQReplayWord 5 136 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 8)
    3264 24 0 (prefix_sizes 8) slice_136
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_137 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3288 3312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_137 :
    generatedNinthLowerSpinSourceQReplayWord 5 137 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 9)
    3288 24 0 (prefix_sizes 9) slice_137
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_138 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3312 3336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_138 :
    generatedNinthLowerSpinSourceQReplayWord 5 138 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 10)
    3312 24 0 (prefix_sizes 10) slice_138
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_139 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3336 3360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_139 :
    generatedNinthLowerSpinSourceQReplayWord 5 139 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 11)
    3336 24 0 (prefix_sizes 11) slice_139
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_140 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3360 3384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_140 :
    generatedNinthLowerSpinSourceQReplayWord 5 140 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 12)
    3360 24 0 (prefix_sizes 12) slice_140
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_141 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3384 3408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_141 :
    generatedNinthLowerSpinSourceQReplayWord 5 141 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 13)
    3384 24 0 (prefix_sizes 13) slice_141
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_142 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3408 3432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_142 :
    generatedNinthLowerSpinSourceQReplayWord 5 142 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 14)
    3408 24 0 (prefix_sizes 14) slice_142
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_143 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3432 3456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_143 :
    generatedNinthLowerSpinSourceQReplayWord 5 143 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 15)
    3432 24 0 (prefix_sizes 15) slice_143
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_08_144 :
    generatedNinthLowerSpinSourceQReplayWord 5 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part08 16)
    3456 24 0 (prefix_sizes 16) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 128 144 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part08 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_08 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨128 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part08.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part08
    128 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (128 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
