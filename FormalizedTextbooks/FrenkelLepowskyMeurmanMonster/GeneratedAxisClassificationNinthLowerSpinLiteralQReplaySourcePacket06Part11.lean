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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 : Fin 17 → Array ℕ :=
  ![
    #[8942817, 10728019, 24692003, 25891552, 2963568, 26207973, 5634511, 26867238,
      24551328, 21853873, 19987343, 19789824, 24691331, 21594949, 1166391, 16884549,
      18696646, 2750100, 5062482, 20243479, 21769908, 17136259, 23086930, 32115455],
    #[14230838, 33220023, 17718640, 31749475, 21583001, 26764862, 21486665, 30943859,
      20393136, 20155520, 21354948, 23894016, 19810752, 6949766, 22956623, 2501510,
      784966, 6154152, 21052910, 5447272, 24286095, 20398528, 7689710, 26164313],
    #[29173316, 16082818, 1133007, 32829941, 21349039, 11849032, 5891800, 27984272,
      2351239, 7676059, 3832648, 22890496, 7598408, 8351691, 18088076, 8347595,
      6047363, 7774128, 23173427, 22552312, 24510916, 3901768, 1544499, 10148579],
    #[26779881, 13846402, 20425167, 13321835, 21676369, 12498971, 21651573, 9502883,
      17790420, 22656456, 2305238, 24881152, 7947291, 24824070, 3334284, 22726918,
      24356125, 7949358, 21461299, 6006837, 8021143, 1166363, 3256627, 27646333],
    #[14961252, 30968217, 7441481, 9136889, 4752565, 9237306, 16837526, 28220655,
      21539617, 21956122, 5393195, 18618368, 6999912, 17873418, 17055177, 22481418,
      24677730, 1187963, 3231001, 2314003, 336545, 7440232, 22320409, 30024082],
    #[12856234, 31725561, 19842776, 9017175, 69512, 26274334, 1188848, 32746808,
      20572452, 3713903, 21721898, 21981184, 24143868, 6918, 24883989, 1366790,
      22107386, 3898264, 21593954, 17874020, 23098601, 17039356, 6932322, 8542456],
    #[29515722, 14181034, 4030581, 10228122, 948342, 12376877, 17502222, 16324715,
      351351, 19745218, 5048138, 25147392, 25125890, 19955462, 4654662, 18005766,
      21889796, 17968230, 21593954, 19937380, 6619716, 19536898, 4847458, 8666360],
    #[12856234, 31725561, 19842776, 9017175, 69512, 26274334, 1188848, 32746808,
      20572452, 3713903, 21721898, 21981184, 24143868, 6918, 24883989, 1366790,
      22107386, 3898264, 21593954, 17874020, 23098601, 17039356, 6932322, 8542456],
    #[14961252, 30968217, 7441481, 9136889, 4752565, 9237306, 16837526, 28220655,
      21539617, 21956122, 5393195, 18618368, 6999912, 17873418, 17055177, 22481418,
      24677730, 1187963, 3231001, 2314003, 336545, 7440232, 22320409, 30024082],
    #[26779881, 13846402, 20425167, 13321835, 21676369, 12498971, 21651573, 9502883,
      17790420, 22656456, 2305238, 24881152, 7947291, 24824070, 3334284, 22726918,
      24356125, 7949358, 21461299, 6006837, 8021143, 1166363, 3256627, 27646333],
    #[29173316, 16082818, 1133007, 32829941, 21349039, 11849032, 5891800, 27984272,
      2351239, 7676059, 3832648, 22890496, 7598408, 8351691, 18088076, 8347595,
      6047363, 7774128, 23173427, 22552312, 24510916, 3901768, 1544499, 10148579],
    #[14230838, 33220023, 17718640, 31749475, 21583001, 26764862, 21486665, 30943859,
      20393136, 20155520, 21354948, 23894016, 19810752, 6949766, 22956623, 2501510,
      784966, 6154152, 21052910, 5447272, 24286095, 20398528, 7689710, 26164313],
    #[8942817, 10728019, 24692003, 25891552, 2963568, 26207973, 5634511, 26867238,
      24551328, 21853873, 19987343, 19789824, 24691331, 21594949, 1166391, 16884549,
      18696646, 2750100, 5062482, 20243479, 21769908, 17136259, 23086930, 32115455],
    #[27715757, 11031559, 18506016, 28403882, 7275217, 27638181, 23879024, 25694169,
      23258264, 2068569, 22361780, 24569856, 6999480, 24866105, 4764432, 24857913,
      5597313, 20491401, 7771144, 2400561, 23629480, 7714232, 19483656, 30362729],
    #[26471008, 11714900, 2125939, 10420020, 6886097, 9109083, 4635715, 8563434,
      24404120, 2762388, 4218905, 23463936, 6322411, 5515975, 21459182, 4467399,
      5667372, 854564, 6684680, 1798863, 24840197, 7282923, 18425864, 31070916],
    #[15206885, 14461424, 841250, 26073067, 1801798, 28090869, 19800269, 16165288,
      1331315, 21675145, 20588225, 17094656, 20315729, 16973684, 1048736, 20074356,
      20506917, 824105, 5970444, 17632632, 18767601, 19584593, 23151116, 29811591],
    #[29462139, 16140483, 18233201, 9351494, 20003605, 28567147, 721408, 16387323,
      19419424, 6941220, 19580609, 18016256, 19209809, 2844810, 3154112, 2869386,
      17940187, 19936794, 22939841, 485451, 573073, 20592209, 7495873, 32736554]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part11 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (13, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part11.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_176 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4224 4248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_176 :
    generatedNinthLowerSpinSourceQReplayWord 6 176 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 0)
    4224 24 0 (prefix_sizes 0) slice_176
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_177 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4248 4272 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_177 :
    generatedNinthLowerSpinSourceQReplayWord 6 177 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 1)
    4248 24 0 (prefix_sizes 1) slice_177
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4248 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_178 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4272 4296 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_178 :
    generatedNinthLowerSpinSourceQReplayWord 6 178 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 2)
    4272 24 0 (prefix_sizes 2) slice_178
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4272 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_179 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4296 4320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_179 :
    generatedNinthLowerSpinSourceQReplayWord 6 179 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 3)
    4296 24 0 (prefix_sizes 3) slice_179
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_180 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4320 4344 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_180 :
    generatedNinthLowerSpinSourceQReplayWord 6 180 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 4)
    4320 24 0 (prefix_sizes 4) slice_180
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4320 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_181 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4344 4368 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_181 :
    generatedNinthLowerSpinSourceQReplayWord 6 181 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 5)
    4344 24 0 (prefix_sizes 5) slice_181
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4344 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_182 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4368 4392 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_182 :
    generatedNinthLowerSpinSourceQReplayWord 6 182 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 6)
    4368 24 0 (prefix_sizes 6) slice_182
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4368 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_183 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4392 4416 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_183 :
    generatedNinthLowerSpinSourceQReplayWord 6 183 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 7)
    4392 24 0 (prefix_sizes 7) slice_183
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4392 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_184 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4416 4440 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_184 :
    generatedNinthLowerSpinSourceQReplayWord 6 184 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 8)
    4416 24 0 (prefix_sizes 8) slice_184
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4416 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_185 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4440 4464 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_185 :
    generatedNinthLowerSpinSourceQReplayWord 6 185 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 9)
    4440 24 0 (prefix_sizes 9) slice_185
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4440 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_186 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4464 4488 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_186 :
    generatedNinthLowerSpinSourceQReplayWord 6 186 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 10)
    4464 24 0 (prefix_sizes 10) slice_186
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4464 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_187 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4488 4512 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_187 :
    generatedNinthLowerSpinSourceQReplayWord 6 187 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 11)
    4488 24 0 (prefix_sizes 11) slice_187
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4488 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_188 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4512 4536 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_188 :
    generatedNinthLowerSpinSourceQReplayWord 6 188 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 12)
    4512 24 0 (prefix_sizes 12) slice_188
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4512 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_189 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4536 4560 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_189 :
    generatedNinthLowerSpinSourceQReplayWord 6 189 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 13)
    4536 24 0 (prefix_sizes 13) slice_189
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4536 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_190 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4560 4584 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_190 :
    generatedNinthLowerSpinSourceQReplayWord 6 190 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 14)
    4560 24 0 (prefix_sizes 14) slice_190
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4560 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_191 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4584 4608 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_191 :
    generatedNinthLowerSpinSourceQReplayWord 6 191 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 15)
    4584 24 0 (prefix_sizes 15) slice_191
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4584 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_192 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4608 4632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_11_192 :
    generatedNinthLowerSpinSourceQReplayWord 6 192 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part11 16)
    4608 24 0 (prefix_sizes 16) slice_192
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 176 192 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_11 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨176 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part11.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part11
    176 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (176 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
