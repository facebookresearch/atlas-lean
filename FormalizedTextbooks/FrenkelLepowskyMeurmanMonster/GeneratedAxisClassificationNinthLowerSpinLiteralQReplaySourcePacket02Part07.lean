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
def generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 : Fin 17 → Array ℕ :=
  ![
    #[9077776, 25633311, 18203721, 28841883, 703185, 10189612, 16837526, 30512249,
      17495363, 17415022, 23641545, 22706176, 8313098, 45054, 17314603, 4456446,
      8163060, 6544927, 23148779, 17049365, 6273569, 2560266, 22145259, 30294676],
    #[30423145, 25978930, 1937112, 29160365, 4018288, 12481835, 1188848, 12828356,
      21343698, 18815136, 19718933, 19965952, 24558346, 3202048, 8117034, 11264,
      6770442, 3138656, 24753002, 5836650, 4010016, 22991626, 22635370, 25465850],
    #[13979332, 11910060, 18413685, 26264222, 1798256, 12063019, 17502222, 13027433,
      6332287, 17770688, 3188294, 19965952, 7786250, 3202048, 25014090, 1051648,
      21433098, 3138656, 4839274, 21584746, 1769536, 7255818, 7939946, 11675642],
    #[30423145, 25978930, 1937112, 29160365, 4018288, 12481835, 1188848, 12828356,
      21343698, 18815136, 19718933, 19965952, 24558346, 3202048, 8117034, 11264,
      6770442, 3138656, 24753002, 5836650, 4010016, 22991626, 22635370, 25465850],
    #[9077776, 25633311, 18203721, 28841883, 703185, 10189612, 16837526, 30512249,
      17495363, 17415022, 23641545, 22706176, 8313098, 45054, 17314603, 4456446,
      8163060, 6544927, 23148779, 17049365, 6273569, 2560266, 22145259, 30294676],
    #[10888398, 13219015, 2507215, 30069622, 8169030, 13494569, 21651573, 27150558,
      3393729, 24222183, 1048716, 19576832, 23552270, 18527334, 17405142, 17728614,
      17694056, 154425, 6475345, 6011447, 20583896, 23775502, 6467153, 27753335],
    #[27866960, 15974900, 17859023, 14440310, 23474965, 14855895, 5891800, 26303296,
      6668, 6802823, 17875084, 20744192, 5551043, 258968, 17232712, 127896,
      497755, 17755658, 6475345, 6610377, 2113675, 8338371, 5422673, 28503514],
    #[33459974, 31632030, 7361904, 27582245, 18398665, 30452666, 21486665, 11023304,
      25142020, 24314690, 19483215, 22890496, 4972148, 485499, 1610180, 288891,
      200207, 1351416, 7559415, 16842892, 3092400, 2893428, 1652983, 9027407],
    #[28438004, 15751797, 4238627, 26110758, 7299212, 9095508, 5634511, 13203595,
      20762884, 7473350, 6597687, 23894016, 20468775, 5686318, 6054799, 1360942,
      4364297, 24198760, 753249, 23591503, 677800, 17738791, 2010721, 27827141],
    #[15549792, 9501732, 7543072, 26513451, 3811919, 14733808, 23879024, 14550960,
      19622144, 17451149, 7066384, 19789824, 1857568, 2989521, 7917236, 6393297,
      7671281, 7607319, 881126, 633911, 3753620, 1310752, 315878, 30641270],
    #[29860947, 8419396, 22669427, 26797336, 3533233, 16527555, 4635715, 29488174,
      17918003, 612896, 24256750, 20695040, 3827776, 19029551, 24881177, 22580783,
      24780399, 7893316, 3671851, 198916, 19583065, 139328, 3254059, 33168264],
    #[14740477, 28639948, 18390562, 10460878, 17459119, 26314364, 19800269, 31776209,
      21872098, 20085285, 3166368, 21067776, 5602240, 3969576, 8085185, 8184360,
      6685160, 24738496, 24445736, 2949376, 18932993, 8336320, 22151976, 13230923],
    #[31079086, 28360801, 1331057, 9670557, 20559202, 10638513, 721408, 16514607,
      7913263, 3280421, 2121920, 22124544, 8161374, 3794053, 8085185, 7951493,
      5940443, 8038509, 6063286, 1507379, 1652383, 6340702, 8094902, 16536966],
    #[15983460, 15316508, 21504730, 16638324, 20028701, 32118877, 964612, 31187496,
      3195428, 24828714, 8141455, 18384896, 17975550, 20465728, 16855688, 17975360,
      2341054, 24345884, 21142946, 5486050, 1636982, 24166654, 21519778, 13939903],
    #[31079086, 28360801, 1331057, 9670557, 20559202, 10638513, 721408, 16514607,
      7913263, 3280421, 2121920, 22124544, 8161374, 3794053, 8085185, 7951493,
      5940443, 8038509, 6063286, 1507379, 1652383, 6340702, 8094902, 16536966],
    #[14740477, 28639948, 18390562, 10460878, 17459119, 26314364, 19800269, 31776209,
      21872098, 20085285, 3166368, 21067776, 5602240, 3969576, 8085185, 8184360,
      6685160, 24738496, 24445736, 2949376, 18932993, 8336320, 22151976, 13230923],
    #[29860947, 8419396, 22669427, 26797336, 3533233, 16527555, 4635715, 29488174,
      17918003, 612896, 24256750, 20695040, 3827776, 19029551, 24881177, 22580783,
      24780399, 7893316, 3671851, 198916, 19583065, 139328, 3254059, 33168264]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters02Part07 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters02Part07.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_112 :
    generatedNinthLowerSpinSourceQReplayWord 2 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 0)
    2688 24 0 (prefix_sizes 0) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_113 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2712 2736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_113 :
    generatedNinthLowerSpinSourceQReplayWord 2 113 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 1)
    2712 24 0 (prefix_sizes 1) slice_113
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_114 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2736 2760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_114 :
    generatedNinthLowerSpinSourceQReplayWord 2 114 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 2)
    2736 24 0 (prefix_sizes 2) slice_114
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_115 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2760 2784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_115 :
    generatedNinthLowerSpinSourceQReplayWord 2 115 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 3)
    2760 24 0 (prefix_sizes 3) slice_115
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_116 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2784 2808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_116 :
    generatedNinthLowerSpinSourceQReplayWord 2 116 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 4)
    2784 24 0 (prefix_sizes 4) slice_116
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_117 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2808 2832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_117 :
    generatedNinthLowerSpinSourceQReplayWord 2 117 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 5)
    2808 24 0 (prefix_sizes 5) slice_117
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_118 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2832 2856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_118 :
    generatedNinthLowerSpinSourceQReplayWord 2 118 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 6)
    2832 24 0 (prefix_sizes 6) slice_118
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_119 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2856 2880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_119 :
    generatedNinthLowerSpinSourceQReplayWord 2 119 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 7)
    2856 24 0 (prefix_sizes 7) slice_119
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_120 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2880 2904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_120 :
    generatedNinthLowerSpinSourceQReplayWord 2 120 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 8)
    2880 24 0 (prefix_sizes 8) slice_120
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_121 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2904 2928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_121 :
    generatedNinthLowerSpinSourceQReplayWord 2 121 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 9)
    2904 24 0 (prefix_sizes 9) slice_121
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_122 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2928 2952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_122 :
    generatedNinthLowerSpinSourceQReplayWord 2 122 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 10)
    2928 24 0 (prefix_sizes 10) slice_122
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_123 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2952 2976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_123 :
    generatedNinthLowerSpinSourceQReplayWord 2 123 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 11)
    2952 24 0 (prefix_sizes 11) slice_123
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_124 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2976 3000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_124 :
    generatedNinthLowerSpinSourceQReplayWord 2 124 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 12)
    2976 24 0 (prefix_sizes 12) slice_124
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_125 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3000 3024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_125 :
    generatedNinthLowerSpinSourceQReplayWord 2 125 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 13)
    3000 24 0 (prefix_sizes 13) slice_125
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_126 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3024 3048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_126 :
    generatedNinthLowerSpinSourceQReplayWord 2 126 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 14)
    3024 24 0 (prefix_sizes 14) slice_126
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_127 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3048 3072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_127 :
    generatedNinthLowerSpinSourceQReplayWord 2 127 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 15)
    3048 24 0 (prefix_sizes 15) slice_127
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_07_128 :
    generatedNinthLowerSpinSourceQReplayWord 2 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part07 16)
    3072 24 0 (prefix_sizes 16) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords02.extract 112 128 =
      generatedNinthLowerSpinLiteralQReplayLetters02Part07 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_02_part_07 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 2 ⟨112 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters02Part07.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords02
    generatedNinthLowerSpinLiteralQReplayLetters02Part07
    112 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords02.getD (112 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
