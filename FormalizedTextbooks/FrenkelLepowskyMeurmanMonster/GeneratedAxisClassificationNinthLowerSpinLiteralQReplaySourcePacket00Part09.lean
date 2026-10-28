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
def generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 : Fin 17 → Array ℕ :=
  ![
    #[32920601, 13823145, 23835267, 10445850, 21354583, 31195981, 3329392, 12477353,
      5288760, 8308794, 20470831, 16992256, 6332859, 4676737, 4960576, 20038785,
      17044794, 3741819, 23704897, 19685824, 25086203, 16888251, 20841793, 29908188],
    #[29569716, 15837796, 24396061, 9491428, 7978340, 30458494, 17353795, 9762458,
      5190822, 22126500, 1228060, 19228672, 6686139, 6450732, 7430163, 17045036,
      17925015, 18046248, 6334143, 3555475, 22302120, 17290683, 509631, 14183612],
    #[14582102, 31269097, 7237569, 10473898, 18964255, 10040027, 8134861, 28449927,
      6962834, 17296788, 22654914, 22857728, 19194195, 5197531, 19173315, 17925851,
      19801992, 1228767, 19550295, 20207244, 5129872, 1712467, 20611159, 27700384],
    #[30214139, 32396868, 6586098, 25974535, 19176882, 28337445, 23056896, 12499412,
      23080865, 743591, 21602210, 21641216, 17092947, 21424421, 17284366, 1630501,
      1130614, 3230994, 1504612, 2204737, 21857373, 1712467, 2495844, 28744896],
    #[27937431, 12490038, 18724714, 29190665, 22146210, 13859618, 17369092, 30689471,
      20757349, 7872145, 23365526, 17577984, 539663, 7419100, 7278588, 21601500,
      18788563, 6840268, 25081631, 5569475, 1252339, 17607695, 20117279, 30127473],
    #[13651844, 11056353, 6696725, 25175541, 21127070, 9365799, 19054860, 13744045,
      23580440, 22348408, 1605515, 17311744, 13, 5537089, 17397608, 16909633,
      7648588, 17022585, 6431541, 6153844, 8204133, 23994381, 8323893, 12436190],
    #[32491445, 26814637, 18309687, 31703709, 3960199, 29222866, 787212, 31731813,
      22720202, 5191897, 18860102, 21968896, 24182013, 1197007, 17927195, 24968143,
      22902578, 22984922, 7948264, 17812519, 21969126, 3874045, 1034216, 31715765],
    #[11114841, 29472659, 2737386, 26525318, 19440450, 9487687, 3439368, 29556496,
      1897591, 848974, 23683522, 17119232, 21782685, 847220, 4745777, 23143796,
      4847081, 2398397, 20198740, 32, 5632684, 3227805, 19490132, 14796451],
    #[9449127, 31737150, 18244372, 29289397, 17318690, 9855303, 19741942, 31132910,
      19947812, 20309968, 21644143, 18024448, 5222960, 17188935, 6183473, 6111303,
      7377527, 2595440, 20873223, 2105408, 6348801, 17060400, 20307975, 31987037],
    #[14336949, 11861316, 19363383, 16040918, 1309989, 8577920, 1869580, 30318647,
      23244579, 21641257, 1510831, 21985280, 22919444, 2146948, 17943579, 23837316,
      4350864, 5893521, 21091841, 16800901, 4701455, 3381524, 20387329, 13382119],
    #[32988118, 16143315, 21375815, 16373621, 8199806, 9366725, 18322782, 14939677,
      7576696, 5767720, 17184953, 24172544, 17565503, 4181953, 24217448, 16975809,
      20517118, 6621355, 19173461, 19208084, 1808471, 563007, 21053525, 15754094],
    #[14143414, 12816670, 7560586, 13849126, 7851853, 9144840, 17082355, 12785277,
      4532344, 21726341, 17014388, 24123392, 17810930, 331506, 5120150, 17811186,
      17171200, 21597592, 513688, 3969130, 17239396, 4019698, 4515480, 29406062],
    #[27048837, 28857649, 21119889, 11484705, 17378516, 29985288, 24442895, 13147596,
      8007577, 17371028, 19416003, 21022720, 19753992, 41988, 3402748, 19377156,
      376844, 4869796, 20539048, 16837292, 20561908, 3562504, 20530856, 32559264],
    #[26271446, 11634383, 5132994, 9035297, 17402036, 14294213, 4782428, 16030879,
      5667530, 440426, 876814, 20973568, 19597320, 3145732, 1705986, 18286596,
      20119564, 24053769, 3801093, 19073025, 3541002, 2492424, 2752517, 29364416],
    #[22066898, 3241671, 5147333, 4797986, 4796599, 1723598, 17316191, 20212889,
      1497800, 4591716, 17658118, 2048, 23818240, 3190784, 5951488, 22523904,
      20168704, 3119104, 3821568, 23322624, 7774208, 6713344, 2772992, 12590286],
    #[24913227, 6144138, 23551098, 1619669, 22939041, 42367, 16779023, 1798256,
      24977543, 24977645, 2574, 2048, 22790144, 5595136, 4239360, 17870848,
      21852160, 2156544, 2510848, 24240128, 6184960, 6209536, 1499136, 14087551],
    #[21791051, 21268340, 6826884, 17756885, 6751839, 2512159, 17155490, 4018288,
      5338580, 7262784, 17566525, 2048, 23920640, 4427776, 4222976, 16814080,
      22773760, 1112064, 2510848, 21049344, 7254016, 6160384, 2551808, 12637471]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters00Part09 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (12, false), (12, false), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (13, true), (14, false), (12, false), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters00Part09.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_144 :
    generatedNinthLowerSpinSourceQReplayWord 0 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 0)
    3456 24 0 (prefix_sizes 0) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_145 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3480 3504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_145 :
    generatedNinthLowerSpinSourceQReplayWord 0 145 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 1)
    3480 24 0 (prefix_sizes 1) slice_145
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_146 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3504 3528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_146 :
    generatedNinthLowerSpinSourceQReplayWord 0 146 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 2)
    3504 24 0 (prefix_sizes 2) slice_146
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_147 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3528 3552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_147 :
    generatedNinthLowerSpinSourceQReplayWord 0 147 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 3)
    3528 24 0 (prefix_sizes 3) slice_147
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_148 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3552 3576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_148 :
    generatedNinthLowerSpinSourceQReplayWord 0 148 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 4)
    3552 24 0 (prefix_sizes 4) slice_148
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_149 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3576 3600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_149 :
    generatedNinthLowerSpinSourceQReplayWord 0 149 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 5)
    3576 24 0 (prefix_sizes 5) slice_149
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_150 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3600 3624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_150 :
    generatedNinthLowerSpinSourceQReplayWord 0 150 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 6)
    3600 24 0 (prefix_sizes 6) slice_150
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_151 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3624 3648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_151 :
    generatedNinthLowerSpinSourceQReplayWord 0 151 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 7)
    3624 24 0 (prefix_sizes 7) slice_151
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_152 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3648 3672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_152 :
    generatedNinthLowerSpinSourceQReplayWord 0 152 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 8)
    3648 24 0 (prefix_sizes 8) slice_152
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_153 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3672 3696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_153 :
    generatedNinthLowerSpinSourceQReplayWord 0 153 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 9)
    3672 24 0 (prefix_sizes 9) slice_153
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_154 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3696 3720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_154 :
    generatedNinthLowerSpinSourceQReplayWord 0 154 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 10)
    3696 24 0 (prefix_sizes 10) slice_154
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_155 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3720 3744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_155 :
    generatedNinthLowerSpinSourceQReplayWord 0 155 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 11)
    3720 24 0 (prefix_sizes 11) slice_155
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_156 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3744 3768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_156 :
    generatedNinthLowerSpinSourceQReplayWord 0 156 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 12)
    3744 24 0 (prefix_sizes 12) slice_156
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_157 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3768 3792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_157 :
    generatedNinthLowerSpinSourceQReplayWord 0 157 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 13)
    3768 24 0 (prefix_sizes 13) slice_157
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_158 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3792 3816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_158 :
    generatedNinthLowerSpinSourceQReplayWord 0 158 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 14)
    3792 24 0 (prefix_sizes 14) slice_158
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_159 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3816 3840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_159 :
    generatedNinthLowerSpinSourceQReplayWord 0 159 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 15)
    3816 24 0 (prefix_sizes 15) slice_159
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_09_160 :
    generatedNinthLowerSpinSourceQReplayWord 0 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part09 16)
    3840 24 0 (prefix_sizes 16) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords00.extract 144 160 =
      generatedNinthLowerSpinLiteralQReplayLetters00Part09 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_00_part_09 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 0 ⟨144 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters00Part09.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords00
    generatedNinthLowerSpinLiteralQReplayLetters00Part09
    144 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords00.getD (144 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
