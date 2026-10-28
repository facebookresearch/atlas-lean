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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 : Fin 17 → Array ℕ :=
  ![
    #[29462139, 16140483, 18233201, 9351494, 20003605, 28567147, 721408, 16387323,
      19419424, 6941220, 19580609, 18016256, 19209809, 2844810, 3154112, 2869386,
      17940187, 19936794, 22939841, 485451, 573073, 20592209, 7495873, 32736554],
    #[30493652, 29662844, 1129178, 16636366, 23926217, 13050084, 964612, 13650591,
      20171309, 7828265, 1686152, 21989376, 17193207, 23259213, 5945999, 17360973,
      23922874, 23918024, 22130034, 21966143, 20996728, 24367351, 4220274, 31634641],
    #[29462139, 16140483, 18233201, 9351494, 20003605, 28567147, 721408, 16387323,
      19419424, 6941220, 19580609, 18016256, 19209809, 2844810, 3154112, 2869386,
      17940187, 19936794, 22939841, 485451, 573073, 20592209, 7495873, 32736554],
    #[15206885, 14461424, 841250, 26073067, 1801798, 28090869, 19800269, 16165288,
      1331315, 21675145, 20588225, 17094656, 20315729, 16973684, 1048736, 20074356,
      20506917, 824105, 5970444, 17632632, 18767601, 19584593, 23151116, 29811591],
    #[26471008, 11714900, 2125939, 10420020, 6886097, 9109083, 4635715, 8563434,
      24404120, 2762388, 4218905, 23463936, 6322411, 5515975, 21459182, 4467399,
      5667372, 854564, 6684680, 1798863, 24840197, 7282923, 18425864, 31070916],
    #[27715757, 11031559, 18506016, 28403882, 7275217, 27638181, 23879024, 25694169,
      23258264, 2068569, 22361780, 24569856, 6999480, 24866105, 4764432, 24857913,
      5597313, 20491401, 7771144, 2400561, 23629480, 7714232, 19483656, 30362729],
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
    #[32273531, 25559656, 18193440, 8557425, 23341267, 15587028, 4259854, 28600094,
      19472592, 17486221, 22705460, 18642944, 18658544, 24448500, 6665784, 21614068,
      19374340, 20347933, 3231001, 686317, 5677768, 19926256, 18380057, 30729836],
    #[13680936, 8746149, 17022016, 27157026, 22608352, 13144185, 22995952, 11695902,
      17367216, 1434131, 7352423, 17451008, 17466608, 25127111, 24125589, 24488135,
      18547767, 18042544, 18401927, 1657408, 21308517, 16784624, 123527, 29480097],
    #[25595937, 15934049, 18406462, 13312299, 17782946, 14892832, 3472278, 27860168,
      21106782, 4904903, 3509278, 18429952, 18277472, 18528112, 20618382, 19576688,
      24689424, 2877348, 21683380, 1323972, 20134126, 20958304, 7623860, 15858541],
    #[11855324, 30944792, 18192097, 16055506, 18819168, 26770903, 3997813, 9174909,
      4395262, 17195142, 19897536, 20027392, 18787871, 3994919, 17790655, 820519,
      6882104, 2987412, 17831596, 20110219, 3233952, 17847839, 5136044, 14415124]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part12 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, true), (13, true), (12, true),
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (13, false), (12, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part12.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_192 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4608 4632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_192 :
    generatedNinthLowerSpinSourceQReplayWord 6 192 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 0)
    4608 24 0 (prefix_sizes 0) slice_192
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_193 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4632 4656 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_193 :
    generatedNinthLowerSpinSourceQReplayWord 6 193 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 1)
    4632 24 0 (prefix_sizes 1) slice_193
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4632 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_194 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4656 4680 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_194 :
    generatedNinthLowerSpinSourceQReplayWord 6 194 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 2)
    4656 24 0 (prefix_sizes 2) slice_194
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4656 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_195 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4680 4704 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_195 :
    generatedNinthLowerSpinSourceQReplayWord 6 195 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 3)
    4680 24 0 (prefix_sizes 3) slice_195
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4680 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_196 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4704 4728 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_196 :
    generatedNinthLowerSpinSourceQReplayWord 6 196 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 4)
    4704 24 0 (prefix_sizes 4) slice_196
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4704 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_197 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4728 4752 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_197 :
    generatedNinthLowerSpinSourceQReplayWord 6 197 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 5)
    4728 24 0 (prefix_sizes 5) slice_197
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4728 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_198 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4752 4776 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_198 :
    generatedNinthLowerSpinSourceQReplayWord 6 198 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 6)
    4752 24 0 (prefix_sizes 6) slice_198
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4752 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_199 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4776 4800 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_199 :
    generatedNinthLowerSpinSourceQReplayWord 6 199 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 7)
    4776 24 0 (prefix_sizes 7) slice_199
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4776 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_200 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4800 4824 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_200 :
    generatedNinthLowerSpinSourceQReplayWord 6 200 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 8)
    4800 24 0 (prefix_sizes 8) slice_200
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4800 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_201 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4824 4848 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_201 :
    generatedNinthLowerSpinSourceQReplayWord 6 201 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 9)
    4824 24 0 (prefix_sizes 9) slice_201
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4824 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_202 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4848 4872 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_202 :
    generatedNinthLowerSpinSourceQReplayWord 6 202 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 10)
    4848 24 0 (prefix_sizes 10) slice_202
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4848 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_203 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4872 4896 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_203 :
    generatedNinthLowerSpinSourceQReplayWord 6 203 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 11)
    4872 24 0 (prefix_sizes 11) slice_203
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4872 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_204 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4896 4920 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_204 :
    generatedNinthLowerSpinSourceQReplayWord 6 204 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 12)
    4896 24 0 (prefix_sizes 12) slice_204
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4896 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_205 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4920 4944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_205 :
    generatedNinthLowerSpinSourceQReplayWord 6 205 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 13)
    4920 24 0 (prefix_sizes 13) slice_205
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_206 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4944 4968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_206 :
    generatedNinthLowerSpinSourceQReplayWord 6 206 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 14)
    4944 24 0 (prefix_sizes 14) slice_206
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_207 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4968 4992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_207 :
    generatedNinthLowerSpinSourceQReplayWord 6 207 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 15)
    4968 24 0 (prefix_sizes 15) slice_207
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_208 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4992 5016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_12_208 :
    generatedNinthLowerSpinSourceQReplayWord 6 208 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part12 16)
    4992 24 0 (prefix_sizes 16) slice_208
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 192 208 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_12 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨192 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part12.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part12
    192 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (192 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
