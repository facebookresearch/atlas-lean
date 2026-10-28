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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 : Fin 17 → Array ℕ :=
  ![
    #[10821542, 26185725, 2080472, 26371170, 17307760, 29573860, 2237424, 27703563,
      23066066, 20011168, 18658069, 19965952, 24042250, 11264, 4944682, 3202048,
      5234442, 4103264, 4215658, 5248874, 1439776, 21410570, 6325098, 31460405],
    #[26640026, 9484437, 22733897, 32529681, 19264209, 8688038, 19962774, 29290227,
      19688771, 22563694, 21097929, 22706176, 1534218, 4456446, 22170411, 45054,
      5664500, 4748831, 6322411, 21380885, 7107105, 5153034, 5286123, 29757470],
    #[9970823, 15512718, 2908623, 27681599, 23879238, 12515680, 18874485, 28579991,
      6168769, 20716007, 4513932, 19576832, 16818446, 17728614, 19082454, 18527334,
      25038184, 2528057, 20315729, 1618487, 24604120, 17631502, 20291153, 9159486],
    #[27427284, 13989744, 20742607, 8618482, 4643605, 25356371, 1402584, 11050436,
      4919820, 1871239, 23249036, 20744192, 3388355, 127896, 20609864, 258968,
      6461531, 19674634, 19209809, 2164169, 8112267, 1588163, 18181713, 28177246],
    #[15519935, 32847143, 3446128, 13901980, 6571465, 11535363, 23460937, 13831281,
      25082628, 22303554, 22358607, 22890496, 921204, 288891, 4577732, 485499,
      4578831, 2574072, 17193207, 24578188, 3651504, 6944372, 23869687, 25778422],
    #[30142381, 12343340, 7912739, 13810047, 19343500, 33524493, 1378767, 31763154,
      24299780, 6416582, 707639, 23894016, 21910567, 1360942, 3210127, 5686318,
      7772169, 20141672, 24976993, 22254159, 1101736, 24685607, 23645793, 25440668],
    #[12757093, 12869921, 4225312, 12627246, 24052303, 14617845, 22048112, 11819701,
      19685632, 17090701, 3539728, 19789824, 2635808, 6393297, 5584564, 2989521,
      884209, 7146519, 23859686, 2413623, 2154132, 2121760, 23441894, 27445619],
    #[13709000, 33256159, 23894131, 30629763, 22413745, 30055000, 7126083, 27528885,
      20336691, 3656224, 18428142, 20695040, 2631744, 22580783, 20996121, 19029551,
      17993327, 7424324, 22652715, 1601796, 16996441, 1073216, 22021931, 8579347],
    #[15992697, 12717640, 24903202, 12448330, 8097711, 13015800, 18997453, 26689877,
      17520098, 23276069, 4100256, 21067776, 7404480, 8184360, 3811009, 3969576,
      258536, 24662720, 1168168, 633088, 21241089, 5944256, 3593000, 26200015],
    #[16278058, 29866213, 6414193, 27748121, 7900514, 15014965, 311808, 12457643,
      2008879, 7585317, 4096192, 22124544, 7276638, 7951493, 2803393, 3794053,
      627931, 8093805, 17732790, 370739, 5975711, 7553118, 19502262, 9049346],
    #[9452327, 12582495, 18375386, 8427831, 7578909, 12582942, 3651588, 26802795,
      3869220, 17947434, 7846543, 18384896, 21612798, 17975360, 18463368, 20465728,
      5388478, 24200476, 3222946, 658914, 6025846, 19611902, 3927458, 9426172],
    #[16278058, 29866213, 6414193, 27748121, 7900514, 15014965, 311808, 12457643,
      2008879, 7585317, 4096192, 22124544, 7276638, 7951493, 2803393, 3794053,
      627931, 8093805, 17732790, 370739, 5975711, 7553118, 19502262, 9049346],
    #[15992697, 12717640, 24903202, 12448330, 8097711, 13015800, 18997453, 26689877,
      17520098, 23276069, 4100256, 21067776, 7404480, 8184360, 3811009, 3969576,
      258536, 24662720, 1168168, 633088, 21241089, 5944256, 3593000, 26200015],
    #[13709000, 33256159, 23894131, 30629763, 22413745, 30055000, 7126083, 27528885,
      20336691, 3656224, 18428142, 20695040, 2631744, 22580783, 20996121, 19029551,
      17993327, 7424324, 22652715, 1601796, 16996441, 1073216, 22021931, 8579347],
    #[12757093, 12869921, 4225312, 12627246, 24052303, 14617845, 22048112, 11819701,
      19685632, 17090701, 3539728, 19789824, 2635808, 6393297, 5584564, 2989521,
      884209, 7146519, 23859686, 2413623, 2154132, 2121760, 23441894, 27445619],
    #[30142381, 12343340, 7912739, 13810047, 19343500, 33524493, 1378767, 31763154,
      24299780, 6416582, 707639, 23894016, 21910567, 1360942, 3210127, 5686318,
      7772169, 20141672, 24976993, 22254159, 1101736, 24685607, 23645793, 25440668],
    #[15519935, 32847143, 3446128, 13901980, 6571465, 11535363, 23460937, 13831281,
      25082628, 22303554, 22358607, 22890496, 921204, 288891, 4577732, 485499,
      4578831, 2574072, 17193207, 24578188, 3651504, 6944372, 23869687, 25778422]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part07 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, false), (13, false), (12, false),
  (12, false), (12, false), (13, false), (12, false),
  (13, false), (12, false), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part07.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_112 :
    generatedNinthLowerSpinSourceQReplayWord 5 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 0)
    2688 24 0 (prefix_sizes 0) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_113 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2712 2736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_113 :
    generatedNinthLowerSpinSourceQReplayWord 5 113 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 1)
    2712 24 0 (prefix_sizes 1) slice_113
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_114 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2736 2760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_114 :
    generatedNinthLowerSpinSourceQReplayWord 5 114 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 2)
    2736 24 0 (prefix_sizes 2) slice_114
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_115 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2760 2784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_115 :
    generatedNinthLowerSpinSourceQReplayWord 5 115 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 3)
    2760 24 0 (prefix_sizes 3) slice_115
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_116 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2784 2808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_116 :
    generatedNinthLowerSpinSourceQReplayWord 5 116 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 4)
    2784 24 0 (prefix_sizes 4) slice_116
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_117 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2808 2832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_117 :
    generatedNinthLowerSpinSourceQReplayWord 5 117 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 5)
    2808 24 0 (prefix_sizes 5) slice_117
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_118 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2832 2856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_118 :
    generatedNinthLowerSpinSourceQReplayWord 5 118 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 6)
    2832 24 0 (prefix_sizes 6) slice_118
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_119 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2856 2880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_119 :
    generatedNinthLowerSpinSourceQReplayWord 5 119 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 7)
    2856 24 0 (prefix_sizes 7) slice_119
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_120 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2880 2904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_120 :
    generatedNinthLowerSpinSourceQReplayWord 5 120 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 8)
    2880 24 0 (prefix_sizes 8) slice_120
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_121 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2904 2928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_121 :
    generatedNinthLowerSpinSourceQReplayWord 5 121 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 9)
    2904 24 0 (prefix_sizes 9) slice_121
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_122 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2928 2952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_122 :
    generatedNinthLowerSpinSourceQReplayWord 5 122 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 10)
    2928 24 0 (prefix_sizes 10) slice_122
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_123 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2952 2976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_123 :
    generatedNinthLowerSpinSourceQReplayWord 5 123 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 11)
    2952 24 0 (prefix_sizes 11) slice_123
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_124 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 2976 3000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_124 :
    generatedNinthLowerSpinSourceQReplayWord 5 124 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 12)
    2976 24 0 (prefix_sizes 12) slice_124
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (2976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_125 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3000 3024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_125 :
    generatedNinthLowerSpinSourceQReplayWord 5 125 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 13)
    3000 24 0 (prefix_sizes 13) slice_125
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_126 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3024 3048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_126 :
    generatedNinthLowerSpinSourceQReplayWord 5 126 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 14)
    3024 24 0 (prefix_sizes 14) slice_126
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_127 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3048 3072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_127 :
    generatedNinthLowerSpinSourceQReplayWord 5 127 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 15)
    3048 24 0 (prefix_sizes 15) slice_127
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_07_128 :
    generatedNinthLowerSpinSourceQReplayWord 5 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part07 16)
    3072 24 0 (prefix_sizes 16) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 112 128 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part07 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_07 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨112 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part07.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part07
    112 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (112 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
