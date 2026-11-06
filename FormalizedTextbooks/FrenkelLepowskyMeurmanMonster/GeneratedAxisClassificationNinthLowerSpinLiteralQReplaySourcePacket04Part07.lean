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
def generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 : Fin 17 → Array ℕ :=
  ![
    #[13752990, 25877143, 4606415, 14103846, 24946246, 30996345, 4874357, 14016142,
      20170945, 225767, 3049612, 2797568, 485646, 3271782, 17530070, 19256422,
      4631912, 6023993, 7351889, 6423095, 22607320, 704782, 7360081, 27819303],
    #[29475316, 30955515, 17984585, 16378495, 17480401, 33337032, 60310, 11061661,
      718147, 6837102, 24221129, 5926912, 24736010, 24373246, 19073835, 3194878,
      17329908, 7437855, 17266923, 17903381, 7547425, 18921738, 20424939, 15335280],
    #[31236948, 29598479, 4409048, 11378832, 20795504, 28294678, 17966064, 9235961,
      4566482, 3244192, 19708693, 3186688, 2650890, 16839680, 3687210, 3148800,
      17411850, 3232864, 17425258, 1668970, 2121760, 6922, 19477354, 15044807],
    #[12973258, 32547234, 21426293, 10199184, 18575472, 10734373, 725006, 26438247,
      23109503, 98496, 2154054, 3186688, 19449610, 18924544, 19449674, 7168,
      596746, 3232864, 1668970, 17425258, 1073216, 19971850, 2721642, 15328756],
    #[31236948, 29598479, 4409048, 11378832, 20795504, 28294678, 17966064, 9235961,
      4566482, 3244192, 19708693, 3186688, 2650890, 16839680, 3687210, 3148800,
      17411850, 3232864, 17425258, 1668970, 2121760, 6922, 19477354, 15044807],
    #[29475316, 30955515, 17984585, 16378495, 17480401, 33337032, 60310, 11061661,
      718147, 6837102, 24221129, 5926912, 24736010, 24373246, 19073835, 3194878,
      17329908, 7437855, 17266923, 17903381, 7547425, 18921738, 20424939, 15335280],
    #[13752990, 25877143, 4606415, 14103846, 24946246, 30996345, 4874357, 14016142,
      20170945, 225767, 3049612, 2797568, 485646, 3271782, 17530070, 19256422,
      4631912, 6023993, 7351889, 6423095, 22607320, 704782, 7360081, 27819303],
    #[14490541, 11889929, 22051279, 31753099, 6697749, 30573098, 22669016, 14618557,
      16783884, 19129735, 19810444, 3964928, 18107331, 20880280, 16911176, 3969944,
      24774747, 24620554, 6692433, 6120905, 6570123, 20956099, 5664337, 26143015],
    #[13303707, 13408771, 5008752, 32020408, 1621449, 31705895, 4709449, 33106773,
      8364804, 3615554, 24576591, 6111232, 24634996, 23531643, 2341316, 6559867,
      23023119, 3198712, 739575, 18442380, 2637744, 17833588, 6367479, 12445650],
    #[13273974, 10665207, 7927075, 13256100, 24076428, 16039894, 22411727, 10601993,
      3985668, 20324550, 4863031, 7114752, 3111, 21171246, 6368143, 66606,
      24053769, 18931304, 7802465, 17711695, 1001384, 3601447, 6479457, 26264903],
    #[15708379, 16185759, 5652768, 28716432, 20589135, 14955595, 7101808, 27154955,
      2844928, 5136525, 670480, 3010560, 20512800, 19604945, 5998260, 6766033,
      22474225, 3572759, 7078374, 7234615, 4150932, 20011040, 6660582, 9454029],
    #[15013352, 14735871, 24813683, 10099875, 20310449, 30970232, 21412931, 8850837,
      1140787, 24883744, 20134126, 3915776, 18423872, 1373743, 22999065, 23997999,
      7339631, 3944772, 6924075, 6553860, 19710041, 18966592, 6293291, 27869747],
    #[10931536, 28320865, 21784098, 13582435, 681903, 9679057, 3023053, 11735932,
      5094882, 3285541, 3233952, 4288512, 16876480, 19786280, 7059137, 7180840,
      19104232, 23616192, 18981672, 6871296, 23393537, 19647424, 17212200, 30252518],
    #[9104387, 10864332, 5654385, 30777648, 3781986, 27288092, 17498624, 11198594,
      24690479, 19035685, 3229888, 5345280, 20873310, 19438725, 7059137, 6825093,
      17421531, 8104045, 980150, 5507123, 4970143, 19056734, 2749622, 31984427],
    #[29147917, 13670005, 17054426, 28989725, 3251485, 10856500, 17741828, 15387201,
      19972644, 1078058, 5157519, 1605632, 6181118, 1302592, 21871240, 20572224,
      21235902, 20086044, 23342498, 6204898, 1600118, 3987710, 24047010, 28687574],
    #[9104387, 10864332, 5654385, 30777648, 3781986, 27288092, 17498624, 11198594,
      24690479, 19035685, 3229888, 5345280, 20873310, 19438725, 7059137, 6825093,
      17421531, 8104045, 980150, 5507123, 4970143, 19056734, 2749622, 31984427],
    #[10931536, 28320865, 21784098, 13582435, 681903, 9679057, 3023053, 11735932,
      5094882, 3285541, 3233952, 4288512, 16876480, 19786280, 7059137, 7180840,
      19104232, 23616192, 18981672, 6871296, 23393537, 19647424, 17212200, 30252518]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters04Part07 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (13, true), (13, false),
  (12, false), (12, false), (13, false), (12, false),
  (12, false), (12, false), (13, false), (12, false),
  (13, false), (12, false), (12, true), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters04Part07.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_112 :
    generatedNinthLowerSpinSourceQReplayWord 4 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 0)
    2688 24 0 (prefix_sizes 0) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_113 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2712 2736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_113 :
    generatedNinthLowerSpinSourceQReplayWord 4 113 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 1)
    2712 24 0 (prefix_sizes 1) slice_113
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_114 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2736 2760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_114 :
    generatedNinthLowerSpinSourceQReplayWord 4 114 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 2)
    2736 24 0 (prefix_sizes 2) slice_114
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_115 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2760 2784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_115 :
    generatedNinthLowerSpinSourceQReplayWord 4 115 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 3)
    2760 24 0 (prefix_sizes 3) slice_115
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_116 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2784 2808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_116 :
    generatedNinthLowerSpinSourceQReplayWord 4 116 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 4)
    2784 24 0 (prefix_sizes 4) slice_116
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_117 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2808 2832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_117 :
    generatedNinthLowerSpinSourceQReplayWord 4 117 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 5)
    2808 24 0 (prefix_sizes 5) slice_117
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_118 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2832 2856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_118 :
    generatedNinthLowerSpinSourceQReplayWord 4 118 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 6)
    2832 24 0 (prefix_sizes 6) slice_118
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_119 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2856 2880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_119 :
    generatedNinthLowerSpinSourceQReplayWord 4 119 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 7)
    2856 24 0 (prefix_sizes 7) slice_119
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_120 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2880 2904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_120 :
    generatedNinthLowerSpinSourceQReplayWord 4 120 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 8)
    2880 24 0 (prefix_sizes 8) slice_120
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_121 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2904 2928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_121 :
    generatedNinthLowerSpinSourceQReplayWord 4 121 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 9)
    2904 24 0 (prefix_sizes 9) slice_121
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_122 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2928 2952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_122 :
    generatedNinthLowerSpinSourceQReplayWord 4 122 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 10)
    2928 24 0 (prefix_sizes 10) slice_122
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_123 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2952 2976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_123 :
    generatedNinthLowerSpinSourceQReplayWord 4 123 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 11)
    2952 24 0 (prefix_sizes 11) slice_123
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_124 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2976 3000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_124 :
    generatedNinthLowerSpinSourceQReplayWord 4 124 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 12)
    2976 24 0 (prefix_sizes 12) slice_124
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_125 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3000 3024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_125 :
    generatedNinthLowerSpinSourceQReplayWord 4 125 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 13)
    3000 24 0 (prefix_sizes 13) slice_125
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_126 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3024 3048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_126 :
    generatedNinthLowerSpinSourceQReplayWord 4 126 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 14)
    3024 24 0 (prefix_sizes 14) slice_126
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_127 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3048 3072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_127 :
    generatedNinthLowerSpinSourceQReplayWord 4 127 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 15)
    3048 24 0 (prefix_sizes 15) slice_127
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_07_128 :
    generatedNinthLowerSpinSourceQReplayWord 4 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part07 16)
    3072 24 0 (prefix_sizes 16) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords04.extract 112 128 =
      generatedNinthLowerSpinLiteralQReplayLetters04Part07 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_04_part_07 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 4 ⟨112 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters04Part07.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords04
    generatedNinthLowerSpinLiteralQReplayLetters04Part07
    112 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords04.getD (112 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
