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
def generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 : Fin 17 → Array ℕ :=
  ![
    #[10931536, 28320865, 21784098, 13582435, 681903, 9679057, 3023053, 11735932,
      5094882, 3285541, 3233952, 4288512, 16876480, 19786280, 7059137, 7180840,
      19104232, 23616192, 18981672, 6871296, 23393537, 19647424, 17212200, 30252518],
    #[15013352, 14735871, 24813683, 10099875, 20310449, 30970232, 21412931, 8850837,
      1140787, 24883744, 20134126, 3915776, 18423872, 1373743, 22999065, 23997999,
      7339631, 3944772, 6924075, 6553860, 19710041, 18966592, 6293291, 27869747],
    #[15708379, 16185759, 5652768, 28716432, 20589135, 14955595, 7101808, 27154955,
      2844928, 5136525, 670480, 3010560, 20512800, 19604945, 5998260, 6766033,
      22474225, 3572759, 7078374, 7234615, 4150932, 20011040, 6660582, 9454029],
    #[13273974, 10665207, 7927075, 13256100, 24076428, 16039894, 22411727, 10601993,
      3985668, 20324550, 4863031, 7114752, 3111, 21171246, 6368143, 66606,
      24053769, 18931304, 7802465, 17711695, 1001384, 3601447, 6479457, 26264903],
    #[13303707, 13408771, 5008752, 32020408, 1621449, 31705895, 4709449, 33106773,
      8364804, 3615554, 24576591, 6111232, 24634996, 23531643, 2341316, 6559867,
      23023119, 3198712, 739575, 18442380, 2637744, 17833588, 6367479, 12445650],
    #[14490541, 11889929, 22051279, 31753099, 6697749, 30573098, 22669016, 14618557,
      16783884, 19129735, 19810444, 3964928, 18107331, 20880280, 16911176, 3969944,
      24774747, 24620554, 6692433, 6120905, 6570123, 20956099, 5664337, 26143015],
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
    #[13370483, 27947116, 8317984, 8559231, 16927441, 25935064, 21037070, 14556186,
      21971668, 4311695, 1080888, 5926912, 18654964, 20908030, 2336052, 1040382,
      23968010, 7437855, 17903381, 17266923, 5944256, 24776436, 22183701, 27192672],
    #[30471456, 9212012, 7216192, 27093473, 18000593, 26069176, 6218736, 12667876,
      21767289, 21547281, 16988309, 8163328, 20525113, 989182, 20525159, 20959230,
      5820359, 24673665, 2837062, 17632696, 7553118, 25126969, 8317510, 11721811],
    #[26590675, 15997665, 3673150, 9455455, 21956166, 30736978, 20249494, 8870314,
      24197342, 16983233, 17360014, 1916928, 3640544, 24751206, 20421662, 7980134,
      20629638, 25131328, 24680902, 22402464, 19611902, 2798816, 23345606, 30184445],
    #[8743614, 8978263, 2442977, 26804469, 23705144, 28957690, 20775029, 15987296,
      23372209, 23655052, 23469759, 2326528, 1875792, 18783261, 2329792, 4953117,
      21584717, 18660300, 2336897, 24552604, 6878096, 6621008, 4003969, 26376043],
    #[27216877, 29182362, 20297345, 12338776, 8007829, 9011194, 947928, 30806189,
      4952655, 6021185, 23010625, 2461696, 2460878, 19631792, 2460832, 5793456,
      24353406, 350290, 2128428, 7775388, 7802990, 5043406, 4114988, 10551750],
    #[27315291, 31095665, 4856136, 12723462, 3837070, 28818794, 18111561, 29659027,
      18375735, 3304509, 17384399, 3137536, 644479, 2660260, 1059984, 23711652,
      8194779, 2112510, 17598757, 4677249, 6523375, 5315967, 18753829, 25751681],
    #[28310001, 28509476, 19857856, 32452080, 26303, 9867025, 4286927, 8933754,
      24099600, 17803794, 24272244, 8056832, 1774288, 3507604, 5944705, 19053972,
      16977732, 3969944, 6563036, 21643592, 23844689, 5749456, 4035804, 26670770]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters04Part08 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (12, false), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters04Part08.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_128 :
    generatedNinthLowerSpinSourceQReplayWord 4 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 0)
    3072 24 0 (prefix_sizes 0) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_129 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3096 3120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_129 :
    generatedNinthLowerSpinSourceQReplayWord 4 129 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 1)
    3096 24 0 (prefix_sizes 1) slice_129
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_130 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3120 3144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_130 :
    generatedNinthLowerSpinSourceQReplayWord 4 130 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 2)
    3120 24 0 (prefix_sizes 2) slice_130
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_131 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3144 3168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_131 :
    generatedNinthLowerSpinSourceQReplayWord 4 131 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 3)
    3144 24 0 (prefix_sizes 3) slice_131
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_132 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3168 3192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_132 :
    generatedNinthLowerSpinSourceQReplayWord 4 132 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 4)
    3168 24 0 (prefix_sizes 4) slice_132
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_133 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3192 3216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_133 :
    generatedNinthLowerSpinSourceQReplayWord 4 133 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 5)
    3192 24 0 (prefix_sizes 5) slice_133
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_134 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3216 3240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_134 :
    generatedNinthLowerSpinSourceQReplayWord 4 134 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 6)
    3216 24 0 (prefix_sizes 6) slice_134
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_135 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3240 3264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_135 :
    generatedNinthLowerSpinSourceQReplayWord 4 135 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 7)
    3240 24 0 (prefix_sizes 7) slice_135
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_136 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3264 3288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_136 :
    generatedNinthLowerSpinSourceQReplayWord 4 136 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 8)
    3264 24 0 (prefix_sizes 8) slice_136
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_137 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3288 3312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_137 :
    generatedNinthLowerSpinSourceQReplayWord 4 137 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 9)
    3288 24 0 (prefix_sizes 9) slice_137
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_138 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3312 3336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_138 :
    generatedNinthLowerSpinSourceQReplayWord 4 138 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 10)
    3312 24 0 (prefix_sizes 10) slice_138
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_139 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3336 3360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_139 :
    generatedNinthLowerSpinSourceQReplayWord 4 139 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 11)
    3336 24 0 (prefix_sizes 11) slice_139
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_140 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3360 3384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_140 :
    generatedNinthLowerSpinSourceQReplayWord 4 140 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 12)
    3360 24 0 (prefix_sizes 12) slice_140
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_141 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3384 3408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_141 :
    generatedNinthLowerSpinSourceQReplayWord 4 141 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 13)
    3384 24 0 (prefix_sizes 13) slice_141
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_142 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3408 3432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_142 :
    generatedNinthLowerSpinSourceQReplayWord 4 142 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 14)
    3408 24 0 (prefix_sizes 14) slice_142
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_143 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3432 3456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_143 :
    generatedNinthLowerSpinSourceQReplayWord 4 143 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 15)
    3432 24 0 (prefix_sizes 15) slice_143
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_08_144 :
    generatedNinthLowerSpinSourceQReplayWord 4 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part08 16)
    3456 24 0 (prefix_sizes 16) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords04.extract 128 144 =
      generatedNinthLowerSpinLiteralQReplayLetters04Part08 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_04_part_08 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 4 ⟨128 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters04Part08.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords04
    generatedNinthLowerSpinLiteralQReplayLetters04Part08
    128 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords04.getD (128 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
