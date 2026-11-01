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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 : Fin 17 → Array ℕ :=
  ![
    #[11855324, 30944792, 18192097, 16055506, 18819168, 26770903, 3997813, 9174909,
      4395262, 17195142, 19897536, 20027392, 18787871, 3994919, 17790655, 820519,
      6882104, 2987412, 17831596, 20110219, 3233952, 17847839, 5136044, 14415124],
    #[10359951, 14391509, 353921, 32366412, 19871840, 26147287, 17725144, 9948718,
      24826624, 18429816, 18848928, 16877568, 478593, 807207, 18253121, 799015,
      7767206, 20385959, 254977, 20036902, 3229888, 3777921, 24992769, 14778407],
    #[26321218, 26318670, 21657928, 9086774, 22217185, 8578124, 1334345, 14478805,
      2056, 528171, 18893968, 23607296, 4864320, 23343058, 19758031, 20000722,
      7495314, 18503313, 8259587, 7167953, 5157519, 4288832, 19099651, 27394014],
    #[28029122, 9956408, 7995840, 14441701, 7507807, 30353214, 21064143, 29458620,
      6275596, 21330728, 20956545, 17823744, 3406796, 2276679, 24556916, 5512519,
      3989131, 1043064, 21529843, 4538804, 24882872, 7062476, 6831347, 14380615],
    #[26077569, 12565731, 5855875, 29211041, 22350069, 15513321, 3329392, 11002718,
      20323076, 19222565, 23032128, 24455168, 5822855, 21428685, 18371631, 18389453,
      4048970, 21209305, 19536019, 3160414, 21745064, 6771079, 5226643, 12263877],
    #[26352159, 10853808, 7383325, 27417183, 7773784, 15520393, 17353795, 25674558,
      17415418, 17176296, 22257683, 23320576, 21925351, 6228531, 1213724, 3258931,
      290772, 22083092, 3549632, 18029555, 22108411, 23143911, 24449472, 28595771],
    #[12332231, 10432428, 22697921, 10841863, 916742, 30237882, 8134861, 30626071,
      24581474, 22328664, 1593283, 20826112, 3218083, 5248486, 18188226, 4052454,
      19171141, 1848774, 1143427, 24981349, 20495713, 6148771, 22039171, 11022356],
    #[9480692, 27323442, 23480050, 8845738, 20483019, 32768804, 23056896, 15926647,
      6567855, 22937611, 883982, 18606080, 1587549, 5481259, 18040738, 566059,
      18408054, 2708331, 545053, 24218166, 1134335, 5378397, 24754461, 11043860],
    #[28996254, 32118241, 5414762, 14217824, 5500024, 8514341, 17369092, 29063388,
      8106859, 18319103, 23007228, 16943104, 16819201, 1971414, 19152790, 3126486,
      7932119, 19027734, 22683585, 17945367, 22481815, 17009665, 1591233, 30027202],
    #[11788917, 12581025, 23856917, 31850981, 20479779, 30100696, 19054860, 29180607,
      19056406, 2294679, 3737448, 19544064, 19544067, 3228739, 3307403, 2765891,
      20689984, 3835588, 22413956, 19005127, 16977800, 19595267, 211588, 27596403],
    #[16315428, 25846931, 5986871, 10217043, 24170788, 31525965, 787212, 26466217,
      1877700, 3434376, 8121371, 21227520, 3343603, 19425485, 17825862, 17615053,
      19178558, 17828985, 862279, 21252234, 21726389, 4074739, 20422727, 11499992],
    #[16151763, 12321138, 24050922, 26067961, 17208097, 16658627, 3439368, 26405225,
      18414713, 2423989, 22919729, 24193024, 3295379, 16830066, 22047170, 19009138,
      20709089, 17408222, 23469631, 6817869, 573777, 7630995, 7362111, 11205567],
    #[14456288, 26862527, 5348116, 9520810, 17580562, 16048624, 19741942, 12418807,
      18696916, 1546872, 22919729, 21100544, 17713600, 1847105, 24333167, 585537,
      2821761, 2523968, 21970369, 8256128, 17904303, 22581696, 5862849, 8980850],
    #[30794045, 28156376, 4935223, 10696634, 5784637, 13211988, 1869580, 28082955,
      19851135, 19527313, 8121371, 23279616, 3424584, 16825812, 1623471, 18996692,
      779420, 1395849, 485397, 6512065, 6362343, 1849672, 20832277, 26061971],
    #[13436183, 13377139, 766791, 14172805, 1271873, 31480762, 18322782, 30385933,
      6911430, 19857575, 3737448, 21469184, 21405313, 23241505, 19673273, 22336289,
      3073440, 21984916, 647988, 24643605, 20008504, 25163393, 22862644, 13754529],
    #[33386871, 31718893, 20452746, 14612197, 18922124, 12586970, 17082355, 16086622,
      24834923, 3507604, 17195158, 24594432, 7376609, 21926418, 20948596, 24699410,
      3331315, 24907865, 19297450, 5091000, 20064405, 7993057, 7707818, 16040556],
    #[29574044, 32359730, 3980177, 14550590, 25156801, 10476071, 24442895, 32533994,
      22927279, 2660260, 21961724, 24918016, 1598526, 7427133, 23641027, 5133373,
      21051395, 1058481, 552626, 21721743, 7544829, 2599998, 24061618, 11237546]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part13 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (12, false), (12, false),
  (13, false), (12, false), (13, false), (12, false),
  (12, false), (12, false), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part13.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_208 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4992 5016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_208 :
    generatedNinthLowerSpinSourceQReplayWord 6 208 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 0)
    4992 24 0 (prefix_sizes 0) slice_208
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_209 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5016 5040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_209 :
    generatedNinthLowerSpinSourceQReplayWord 6 209 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 1)
    5016 24 0 (prefix_sizes 1) slice_209
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_210 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5040 5064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_210 :
    generatedNinthLowerSpinSourceQReplayWord 6 210 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 2)
    5040 24 0 (prefix_sizes 2) slice_210
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_211 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5064 5088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_211 :
    generatedNinthLowerSpinSourceQReplayWord 6 211 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 3)
    5064 24 0 (prefix_sizes 3) slice_211
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_212 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5088 5112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_212 :
    generatedNinthLowerSpinSourceQReplayWord 6 212 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 4)
    5088 24 0 (prefix_sizes 4) slice_212
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_213 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5112 5136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_213 :
    generatedNinthLowerSpinSourceQReplayWord 6 213 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 5)
    5112 24 0 (prefix_sizes 5) slice_213
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_214 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5136 5160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_214 :
    generatedNinthLowerSpinSourceQReplayWord 6 214 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 6)
    5136 24 0 (prefix_sizes 6) slice_214
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_215 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5160 5184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_215 :
    generatedNinthLowerSpinSourceQReplayWord 6 215 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 7)
    5160 24 0 (prefix_sizes 7) slice_215
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_216 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5184 5208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_216 :
    generatedNinthLowerSpinSourceQReplayWord 6 216 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 8)
    5184 24 0 (prefix_sizes 8) slice_216
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_217 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5208 5232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_217 :
    generatedNinthLowerSpinSourceQReplayWord 6 217 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 9)
    5208 24 0 (prefix_sizes 9) slice_217
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_218 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5232 5256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_218 :
    generatedNinthLowerSpinSourceQReplayWord 6 218 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 10)
    5232 24 0 (prefix_sizes 10) slice_218
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_219 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5256 5280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_219 :
    generatedNinthLowerSpinSourceQReplayWord 6 219 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 11)
    5256 24 0 (prefix_sizes 11) slice_219
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_220 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5280 5304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_220 :
    generatedNinthLowerSpinSourceQReplayWord 6 220 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 12)
    5280 24 0 (prefix_sizes 12) slice_220
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_221 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5304 5328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_221 :
    generatedNinthLowerSpinSourceQReplayWord 6 221 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 13)
    5304 24 0 (prefix_sizes 13) slice_221
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_222 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5328 5352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_222 :
    generatedNinthLowerSpinSourceQReplayWord 6 222 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 14)
    5328 24 0 (prefix_sizes 14) slice_222
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_223 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5352 5376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_223 :
    generatedNinthLowerSpinSourceQReplayWord 6 223 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 15)
    5352 24 0 (prefix_sizes 15) slice_223
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_224 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5376 5400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_13_224 :
    generatedNinthLowerSpinSourceQReplayWord 6 224 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part13 16)
    5376 24 0 (prefix_sizes 16) slice_224
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 208 224 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_13 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨208 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part13.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part13
    208 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (208 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
