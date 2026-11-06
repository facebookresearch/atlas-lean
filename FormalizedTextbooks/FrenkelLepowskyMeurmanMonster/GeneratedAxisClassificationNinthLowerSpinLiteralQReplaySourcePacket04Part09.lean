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
def generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 : Fin 17 → Array ℕ :=
  ![
    #[28310001, 28509476, 19857856, 32452080, 26303, 9867025, 4286927, 8933754,
      24099600, 17803794, 24272244, 8056832, 1774288, 3507604, 5944705, 19053972,
      16977732, 3969944, 6563036, 21643592, 23844689, 5749456, 4035804, 26670770],
    #[12194927, 25461983, 19921539, 25504876, 22708311, 30546747, 20106608, 14877663,
      5485368, 19111994, 19688495, 212992, 19390907, 5665921, 4436288, 18934913,
      22183226, 6559867, 6479169, 3549632, 3244283, 21428667, 3501377, 13122730],
    #[11978044, 11040236, 20371741, 9690220, 6743396, 31571446, 576579, 14680338,
      4859046, 3815332, 1096988, 2449408, 18974139, 6514220, 5853203, 17112620,
      22481815, 21531944, 25034431, 19536019, 3929512, 20995515, 18521791, 32983860],
    #[13782499, 30807132, 284609, 13915423, 17745695, 29087342, 24912077, 16764978,
      7089810, 7091604, 22720450, 6078464, 4768083, 935643, 23359427, 22056667,
      16977800, 1249247, 444503, 5885580, 23236240, 7735635, 1448023, 32165909],
    #[30580099, 16135228, 3704562, 13911423, 20649394, 27387741, 6279680, 15778732,
      23478177, 22429863, 21794722, 4861952, 6173011, 18284837, 22527246, 4786469,
      1722486, 2153746, 17591652, 23780417, 4680797, 4245843, 20745572, 32077496],
    #[8604238, 15646191, 22364010, 16270032, 21914786, 28468219, 591876, 12572774,
      24685413, 17671825, 23238550, 798720, 17083407, 3386588, 1093628, 17499356,
      22067411, 4181964, 6762271, 17822659, 23077875, 16790543, 2846495, 33011112],
    #[26493898, 27123887, 788245, 26001851, 22927262, 8842601, 2277644, 16747491,
      24104728, 4618872, 6057867, 532480, 23207949, 4080961, 18487144, 23608641,
      8170828, 22036089, 20560693, 23875188, 17590117, 17565709, 19176245, 12615312],
    #[14093189, 8826013, 18123319, 14952109, 2352519, 26096610, 17564428, 13634645,
      22458058, 23564505, 18335814, 5189632, 8330493, 2014159, 20331547, 24118223,
      22966066, 21637338, 24039400, 1356839, 6775014, 3470589, 18370536, 12803461],
    #[28561334, 13048188, 1572074, 16490601, 20392770, 13339560, 20216584, 15698431,
      5829751, 23739470, 23421378, 339968, 3559581, 3917172, 2603569, 22416756,
      323049, 7997629, 2604372, 19179552, 20978348, 4946077, 3861844, 26353740],
    #[9800662, 13310031, 19421972, 32040644, 19389218, 32648246, 2964726, 15305119,
      22184228, 4444112, 20992879, 1245184, 18047536, 20013127, 2189873, 6973511,
      1796727, 6941296, 1771527, 20088896, 21170177, 22579760, 1075207, 9756716],
    #[13082485, 25897348, 19177015, 16131862, 828709, 28387136, 18646796, 14617847,
      21905187, 4702249, 1711535, 5206016, 7522580, 2898564, 18033691, 23544452,
      6417296, 6827409, 5479937, 2024581, 23733519, 1892628, 2448897, 32267559],
    #[27985864, 32921549, 19661639, 33043307, 4753022, 26015963, 1545566, 13998595,
      7261304, 24324648, 21313721, 7393280, 8091455, 5633985, 22722408, 23674817,
      19159294, 972971, 5376085, 3784596, 21483607, 8384319, 3659861, 11394928],
    #[10645590, 15509246, 2073994, 33392070, 5531469, 25202152, 305139, 15358365,
      5130360, 7773317, 21384820, 7344128, 6837746, 5895922, 4403350, 22232818,
      20802304, 18128280, 23178904, 17176682, 7177572, 5950962, 19046040, 11857038],
    #[32406448, 9964804, 19913617, 10901012, 22824148, 10502717, 7665679, 14487033,
      847769, 4245396, 21971907, 4243456, 3554312, 6814724, 7400444, 21033988,
      7981068, 274084, 724648, 5624492, 6416372, 2950152, 732840, 11214997],
    #[29464622, 10790967, 338626, 8769753, 21631156, 27677245, 21559644, 30567015,
      2128586, 25141354, 6988046, 4194304, 1472520, 4700164, 6281218, 23113732,
      24758284, 16881673, 18765829, 7397377, 21929994, 1798152, 17717253, 25720376],
    #[8490025, 31728698, 4584141, 8733906, 21670078, 10909237, 538975, 26406502,
      23122632, 25102442, 6994186, 20973568, 5636104, 17238020, 18810882, 6293508,
      20514828, 4259849, 6160389, 24119297, 21891082, 1769480, 5111813, 17303096],
    #[15659054, 9291757, 2920054, 8834383, 2431056, 14196762, 1807, 16127001,
      4802695, 1005795, 21680398, 21960704, 7039500, 23445772, 17214222, 2101516,
      5077760, 1123825, 1545969, 20944893, 6799618, 2193932, 2565873, 679143]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters04Part09 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, false), (12, false), (12, false),
  (13, true), (12, true), (12, true), (13, true),
  (12, true), (13, true), (14, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters04Part09.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_144 :
    generatedNinthLowerSpinSourceQReplayWord 4 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 0)
    3456 24 0 (prefix_sizes 0) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_145 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3480 3504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_145 :
    generatedNinthLowerSpinSourceQReplayWord 4 145 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 1)
    3480 24 0 (prefix_sizes 1) slice_145
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_146 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3504 3528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_146 :
    generatedNinthLowerSpinSourceQReplayWord 4 146 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 2)
    3504 24 0 (prefix_sizes 2) slice_146
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_147 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3528 3552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_147 :
    generatedNinthLowerSpinSourceQReplayWord 4 147 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 3)
    3528 24 0 (prefix_sizes 3) slice_147
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_148 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3552 3576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_148 :
    generatedNinthLowerSpinSourceQReplayWord 4 148 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 4)
    3552 24 0 (prefix_sizes 4) slice_148
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_149 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3576 3600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_149 :
    generatedNinthLowerSpinSourceQReplayWord 4 149 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 5)
    3576 24 0 (prefix_sizes 5) slice_149
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_150 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3600 3624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_150 :
    generatedNinthLowerSpinSourceQReplayWord 4 150 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 6)
    3600 24 0 (prefix_sizes 6) slice_150
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_151 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3624 3648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_151 :
    generatedNinthLowerSpinSourceQReplayWord 4 151 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 7)
    3624 24 0 (prefix_sizes 7) slice_151
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_152 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3648 3672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_152 :
    generatedNinthLowerSpinSourceQReplayWord 4 152 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 8)
    3648 24 0 (prefix_sizes 8) slice_152
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_153 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3672 3696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_153 :
    generatedNinthLowerSpinSourceQReplayWord 4 153 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 9)
    3672 24 0 (prefix_sizes 9) slice_153
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_154 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3696 3720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_154 :
    generatedNinthLowerSpinSourceQReplayWord 4 154 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 10)
    3696 24 0 (prefix_sizes 10) slice_154
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_155 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3720 3744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_155 :
    generatedNinthLowerSpinSourceQReplayWord 4 155 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 11)
    3720 24 0 (prefix_sizes 11) slice_155
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_156 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3744 3768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_156 :
    generatedNinthLowerSpinSourceQReplayWord 4 156 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 12)
    3744 24 0 (prefix_sizes 12) slice_156
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_157 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3768 3792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_157 :
    generatedNinthLowerSpinSourceQReplayWord 4 157 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 13)
    3768 24 0 (prefix_sizes 13) slice_157
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_158 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3792 3816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_158 :
    generatedNinthLowerSpinSourceQReplayWord 4 158 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 14)
    3792 24 0 (prefix_sizes 14) slice_158
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_159 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3816 3840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_159 :
    generatedNinthLowerSpinSourceQReplayWord 4 159 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 15)
    3816 24 0 (prefix_sizes 15) slice_159
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_09_160 :
    generatedNinthLowerSpinSourceQReplayWord 4 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part09 16)
    3840 24 0 (prefix_sizes 16) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords04.extract 144 160 =
      generatedNinthLowerSpinLiteralQReplayLetters04Part09 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_04_part_09 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 4 ⟨144 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters04Part09.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords04
    generatedNinthLowerSpinLiteralQReplayLetters04Part09
    144 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords04.getD (144 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
