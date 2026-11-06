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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 : Fin 17 → Array ℕ :=
  ![
    #[11654684, 16536231, 3924777, 31808984, 2985384, 32122688, 984048, 26793367,
      1218866, 3901775, 3146556, 3006464, 5124635, 3264806, 4441085, 21117222,
      3943229, 6683721, 3577716, 24497746, 16849382, 7461403, 24424308, 11074982],
    #[11653066, 15867541, 8120280, 27860033, 21178000, 29592630, 24538006, 25536626,
      3973651, 2647103, 5890585, 7991296, 18132427, 20484143, 3311467, 7981103,
      1975780, 18155983, 5557291, 3736580, 1970848, 22996427, 22344747, 11531934],
    #[16200827, 9050996, 4512837, 25310147, 19375493, 31263981, 22491253, 30024159,
      1124295, 284, 19799749, 4276224, 1336194, 24925650, 7090408, 7040466,
      5529168, 5270896, 107296, 1212146, 527210, 4344706, 21859104, 10724747],
    #[31306024, 26451082, 21457544, 28385550, 975387, 33484352, 5408472, 13246943,
      303370, 19722287, 2652869, 7442432, 168834, 24729471, 4891880, 8277887,
      4308221, 23903299, 17739966, 1617857, 18390890, 6581122, 5531838, 27509227],
    #[14254113, 9613235, 18453319, 9256962, 23834059, 8713274, 22862921, 32122432,
      21829902, 22144466, 17869946, 1589248, 4436553, 17693396, 7998812, 582356,
      2826397, 2220237, 2953296, 8323716, 2889493, 3426889, 23963728, 14870109],
    #[29513180, 31009627, 20696631, 10285838, 7144322, 32638957, 2836943, 12799034,
      4577282, 23362883, 18041901, 2785280, 17337909, 5218487, 20999170, 21608631,
      5568130, 6616690, 708848, 21030983, 18569783, 17745461, 18929904, 29340663],
    #[30154061, 10556935, 17287956, 16263174, 2900553, 16573349, 20000112, 30543853,
      4594446, 1188033, 3299618, 2551808, 22255642, 20129185, 19582192, 7814561,
      2233787, 2258469, 983966, 1248831, 2223338, 17735706, 16829342, 8650345],
    #[31714995, 27828633, 556266, 33005560, 20764233, 14710422, 1907779, 16707262,
      21420814, 115212, 2603919, 1499136, 24825828, 19711583, 20774128, 8269407,
      3293627, 20062757, 20911006, 17624513, 3037972, 16848868, 3201950, 9665033],
    #[32619351, 15671170, 20321874, 29621860, 19147211, 10243975, 24477901, 11859882,
      24403974, 17742596, 7976628, 491520, 7278164, 24858873, 20417632, 8112377,
      17151661, 20522196, 22082169, 22100608, 21912116, 7239252, 6945401, 13170165],
    #[15007130, 15671170, 20629249, 14071977, 20217291, 12572970, 5665280, 28459978,
      6158328, 17902842, 23785497, 491520, 8145145, 7878228, 20417632, 23629396,
      374445, 17404084, 24557081, 23259213, 5061785, 7147769, 5226009, 12665451],
    #[9243791, 27217335, 12299, 12668575, 2405250, 15747887, 3016708, 10275717,
      2549348, 23954786, 1296065, 2306048, 163439, 1111558, 17458719, 21323270,
      7110761, 17561938, 20003131, 8329021, 19935344, 7005807, 4997435, 13731610],
    #[15007130, 15671170, 20629249, 14071977, 20217291, 12572970, 5665280, 28459978,
      6158328, 17902842, 23785497, 491520, 8145145, 7878228, 20417632, 23629396,
      374445, 17404084, 24557081, 23259213, 5061785, 7147769, 5226009, 12665451],
    #[32619351, 15671170, 20321874, 29621860, 19147211, 10243975, 24477901, 11859882,
      24403974, 17742596, 7976628, 491520, 7278164, 24858873, 20417632, 8112377,
      17151661, 20522196, 22082169, 22100608, 21912116, 7239252, 6945401, 13170165],
    #[31714995, 27828633, 556266, 33005560, 20764233, 14710422, 1907779, 16707262,
      21420814, 115212, 2603919, 1499136, 24825828, 19711583, 20774128, 8269407,
      3293627, 20062757, 20911006, 17624513, 3037972, 16848868, 3201950, 9665033],
    #[30154061, 10556935, 17287956, 16263174, 2900553, 16573349, 20000112, 30543853,
      4594446, 1188033, 3299618, 2551808, 22255642, 20129185, 19582192, 7814561,
      2233787, 2258469, 983966, 1248831, 2223338, 17735706, 16829342, 8650345],
    #[29513180, 31009627, 20696631, 10285838, 7144322, 32638957, 2836943, 12799034,
      4577282, 23362883, 18041901, 2785280, 17337909, 5218487, 20999170, 21608631,
      5568130, 6616690, 708848, 21030983, 18569783, 17745461, 18929904, 29340663],
    #[14254113, 9613235, 18453319, 9256962, 23834059, 8713274, 22862921, 32122432,
      21829902, 22144466, 17869946, 1589248, 4436553, 17693396, 7998812, 582356,
      2826397, 2220237, 2953296, 8323716, 2889493, 3426889, 23963728, 14870109]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part09 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, false), (13, false), (12, false),
  (12, false), (12, false), (13, false), (12, false),
  (13, false), (12, false), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part09.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_144 :
    generatedNinthLowerSpinSourceQReplayWord 7 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 0)
    3456 24 0 (prefix_sizes 0) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_145 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3480 3504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_145 :
    generatedNinthLowerSpinSourceQReplayWord 7 145 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 1)
    3480 24 0 (prefix_sizes 1) slice_145
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_146 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3504 3528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_146 :
    generatedNinthLowerSpinSourceQReplayWord 7 146 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 2)
    3504 24 0 (prefix_sizes 2) slice_146
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_147 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3528 3552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_147 :
    generatedNinthLowerSpinSourceQReplayWord 7 147 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 3)
    3528 24 0 (prefix_sizes 3) slice_147
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_148 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3552 3576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_148 :
    generatedNinthLowerSpinSourceQReplayWord 7 148 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 4)
    3552 24 0 (prefix_sizes 4) slice_148
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_149 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3576 3600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_149 :
    generatedNinthLowerSpinSourceQReplayWord 7 149 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 5)
    3576 24 0 (prefix_sizes 5) slice_149
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_150 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3600 3624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_150 :
    generatedNinthLowerSpinSourceQReplayWord 7 150 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 6)
    3600 24 0 (prefix_sizes 6) slice_150
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_151 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3624 3648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_151 :
    generatedNinthLowerSpinSourceQReplayWord 7 151 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 7)
    3624 24 0 (prefix_sizes 7) slice_151
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_152 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3648 3672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_152 :
    generatedNinthLowerSpinSourceQReplayWord 7 152 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 8)
    3648 24 0 (prefix_sizes 8) slice_152
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_153 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3672 3696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_153 :
    generatedNinthLowerSpinSourceQReplayWord 7 153 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 9)
    3672 24 0 (prefix_sizes 9) slice_153
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_154 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3696 3720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_154 :
    generatedNinthLowerSpinSourceQReplayWord 7 154 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 10)
    3696 24 0 (prefix_sizes 10) slice_154
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_155 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3720 3744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_155 :
    generatedNinthLowerSpinSourceQReplayWord 7 155 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 11)
    3720 24 0 (prefix_sizes 11) slice_155
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_156 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3744 3768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_156 :
    generatedNinthLowerSpinSourceQReplayWord 7 156 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 12)
    3744 24 0 (prefix_sizes 12) slice_156
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_157 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3768 3792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_157 :
    generatedNinthLowerSpinSourceQReplayWord 7 157 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 13)
    3768 24 0 (prefix_sizes 13) slice_157
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_158 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3792 3816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_158 :
    generatedNinthLowerSpinSourceQReplayWord 7 158 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 14)
    3792 24 0 (prefix_sizes 14) slice_158
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_159 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3816 3840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_159 :
    generatedNinthLowerSpinSourceQReplayWord 7 159 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 15)
    3816 24 0 (prefix_sizes 15) slice_159
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_09_160 :
    generatedNinthLowerSpinSourceQReplayWord 7 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part09 16)
    3840 24 0 (prefix_sizes 16) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 144 160 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part09 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_09 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨144 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part09.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part09
    144 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (144 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
