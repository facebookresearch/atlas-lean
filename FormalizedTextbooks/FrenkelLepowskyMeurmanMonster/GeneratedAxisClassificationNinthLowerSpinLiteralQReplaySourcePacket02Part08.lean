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
def generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 : Fin 17 → Array ℕ :=
  ![
    #[29860947, 8419396, 22669427, 26797336, 3533233, 16527555, 4635715, 29488174,
      17918003, 612896, 24256750, 20695040, 3827776, 19029551, 24881177, 22580783,
      24780399, 7893316, 3671851, 198916, 19583065, 139328, 3254059, 33168264],
    #[15549792, 9501732, 7543072, 26513451, 3811919, 14733808, 23879024, 14550960,
      19622144, 17451149, 7066384, 19789824, 1857568, 2989521, 7917236, 6393297,
      7671281, 7607319, 881126, 633911, 3753620, 1310752, 315878, 30641270],
    #[28438004, 15751797, 4238627, 26110758, 7299212, 9095508, 5634511, 13203595,
      20762884, 7473350, 6597687, 23894016, 20468775, 5686318, 6054799, 1360942,
      4364297, 24198760, 753249, 23591503, 677800, 17738791, 2010721, 27827141],
    #[33459974, 31632030, 7361904, 27582245, 18398665, 30452666, 21486665, 11023304,
      25142020, 24314690, 19483215, 22890496, 4972148, 485499, 1610180, 288891,
      200207, 1351416, 7559415, 16842892, 3092400, 2893428, 1652983, 9027407],
    #[27866960, 15974900, 17859023, 14440310, 23474965, 14855895, 5891800, 26303296,
      6668, 6802823, 17875084, 20744192, 5551043, 258968, 17232712, 127896,
      497755, 17755658, 6475345, 6610377, 2113675, 8338371, 5422673, 28503514],
    #[10888398, 13219015, 2507215, 30069622, 8169030, 13494569, 21651573, 27150558,
      3393729, 24222183, 1048716, 19576832, 23552270, 18527334, 17405142, 17728614,
      17694056, 154425, 6475345, 6011447, 20583896, 23775502, 6467153, 27753335],
    #[9077776, 25633311, 18203721, 28841883, 703185, 10189612, 16837526, 30512249,
      17495363, 17415022, 23641545, 22706176, 8313098, 45054, 17314603, 4456446,
      8163060, 6544927, 23148779, 17049365, 6273569, 2560266, 22145259, 30294676],
    #[30423145, 25978930, 1937112, 29160365, 4018288, 12481835, 1188848, 12828356,
      21343698, 18815136, 19718933, 19965952, 24558346, 3202048, 8117034, 11264,
      6770442, 3138656, 24753002, 5836650, 4010016, 22991626, 22635370, 25465850],
    #[13979332, 11910060, 18413685, 26264222, 1798256, 12063019, 17502222, 13027433,
      6332287, 17770688, 3188294, 19965952, 7786250, 3202048, 25014090, 1051648,
      21433098, 3138656, 4839274, 21584746, 1769536, 7255818, 7939946, 11675642],
    #[30999673, 10735718, 4604960, 14234229, 150225, 8764626, 4259854, 25302032,
      5194452, 23904911, 8050232, 22706176, 2363124, 45054, 3380, 3178494,
      6994186, 6544927, 17075989, 19755243, 4305856, 4368116, 21487381, 30467434],
    #[15491796, 25855896, 7767104, 13608469, 1223377, 27025228, 22995952, 25429008,
      4990073, 5488913, 21983381, 24942592, 2205753, 19972094, 17606759, 16805886,
      25165767, 22863233, 2677318, 20002232, 6176862, 6811705, 8223302, 31687591],
    #[30967991, 11497349, 2266174, 13404731, 5178950, 10352438, 3472278, 29889742,
      7420126, 8232129, 18205838, 18696192, 19731680, 2479206, 19448862, 2471014,
      8136838, 22919488, 18659782, 23956896, 19824894, 19934432, 16783814, 16023193],
    #[16088481, 9791560, 3989217, 15437802, 6927928, 16764133, 3997813, 31128959,
      6594993, 3508876, 17864383, 19105792, 17106768, 8332317, 791744, 2761757,
      3242829, 18906060, 6768769, 22281372, 6222736, 24944464, 7993473, 27531380],
    #[13266527, 9641000, 18628225, 32369642, 24785045, 15358536, 17725144, 30067999,
      21729871, 16795713, 17392961, 19240960, 17564878, 8054448, 3802272, 591536,
      752254, 1022034, 5397036, 5631132, 4264046, 23428302, 5040684, 25332852],
    #[11163897, 29073363, 3072328, 11110820, 20614286, 12999112, 1334345, 29303601,
      1598519, 23708733, 23591887, 19916800, 23932287, 21184420, 1025168, 16936868,
      24271579, 1063934, 20175141, 1287809, 1636847, 20309375, 18970917, 31198243],
    #[8789615, 12657338, 22804928, 25440878, 16803519, 30677135, 21064143, 30670564,
      7322384, 5505554, 18847092, 24836096, 24111824, 22961556, 4537729, 21589396,
      1847108, 844696, 4945116, 17746248, 16820049, 19088080, 1230044, 30587180],
    #[31633896, 13795672, 23835267, 14856683, 5931095, 13729468, 3329392, 30539352,
      22262584, 7866426, 22656047, 16992256, 6531515, 23575681, 6043968, 17902721,
      2620730, 948347, 8207681, 1573312, 6963451, 176571, 2788673, 28328237]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters02Part08 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters02Part08.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_128 :
    generatedNinthLowerSpinSourceQReplayWord 2 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 0)
    3072 24 0 (prefix_sizes 0) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_129 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3096 3120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_129 :
    generatedNinthLowerSpinSourceQReplayWord 2 129 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 1)
    3096 24 0 (prefix_sizes 1) slice_129
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_130 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3120 3144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_130 :
    generatedNinthLowerSpinSourceQReplayWord 2 130 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 2)
    3120 24 0 (prefix_sizes 2) slice_130
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_131 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3144 3168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_131 :
    generatedNinthLowerSpinSourceQReplayWord 2 131 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 3)
    3144 24 0 (prefix_sizes 3) slice_131
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_132 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3168 3192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_132 :
    generatedNinthLowerSpinSourceQReplayWord 2 132 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 4)
    3168 24 0 (prefix_sizes 4) slice_132
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_133 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3192 3216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_133 :
    generatedNinthLowerSpinSourceQReplayWord 2 133 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 5)
    3192 24 0 (prefix_sizes 5) slice_133
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_134 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3216 3240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_134 :
    generatedNinthLowerSpinSourceQReplayWord 2 134 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 6)
    3216 24 0 (prefix_sizes 6) slice_134
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_135 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3240 3264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_135 :
    generatedNinthLowerSpinSourceQReplayWord 2 135 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 7)
    3240 24 0 (prefix_sizes 7) slice_135
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_136 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3264 3288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_136 :
    generatedNinthLowerSpinSourceQReplayWord 2 136 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 8)
    3264 24 0 (prefix_sizes 8) slice_136
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_137 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3288 3312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_137 :
    generatedNinthLowerSpinSourceQReplayWord 2 137 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 9)
    3288 24 0 (prefix_sizes 9) slice_137
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_138 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3312 3336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_138 :
    generatedNinthLowerSpinSourceQReplayWord 2 138 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 10)
    3312 24 0 (prefix_sizes 10) slice_138
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_139 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3336 3360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_139 :
    generatedNinthLowerSpinSourceQReplayWord 2 139 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 11)
    3336 24 0 (prefix_sizes 11) slice_139
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_140 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3360 3384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_140 :
    generatedNinthLowerSpinSourceQReplayWord 2 140 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 12)
    3360 24 0 (prefix_sizes 12) slice_140
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_141 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3384 3408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_141 :
    generatedNinthLowerSpinSourceQReplayWord 2 141 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 13)
    3384 24 0 (prefix_sizes 13) slice_141
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_142 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3408 3432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_142 :
    generatedNinthLowerSpinSourceQReplayWord 2 142 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 14)
    3408 24 0 (prefix_sizes 14) slice_142
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_143 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3432 3456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_143 :
    generatedNinthLowerSpinSourceQReplayWord 2 143 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 15)
    3432 24 0 (prefix_sizes 15) slice_143
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_08_144 :
    generatedNinthLowerSpinSourceQReplayWord 2 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part08 16)
    3456 24 0 (prefix_sizes 16) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords02.extract 128 144 =
      generatedNinthLowerSpinLiteralQReplayLetters02Part08 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_02_part_08 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 2 ⟨128 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters02Part08.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords02
    generatedNinthLowerSpinLiteralQReplayLetters02Part08
    128 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords02.getD (128 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
