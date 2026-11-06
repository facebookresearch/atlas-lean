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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 : Fin 17 → Array ℕ :=
  ![
    #[26669227, 25584811, 20300832, 12216254, 24320211, 10357013, 4325390, 14447315,
      22902578, 24934797, 5873882, 1880064, 486162, 21788952, 18594516, 17549592,
      4655626, 16787212, 6991110, 22823966, 4575686, 22047506, 7863558, 27416752],
    #[33056751, 29828029, 579701, 28838021, 5187702, 30816816, 17371150, 10484094,
      7648588, 24658370, 4699769, 6270976, 22795577, 26175, 21223295, 1353279,
      22653702, 4339038, 5099096, 22190183, 17850950, 1615161, 3886680, 13849813],
    #[33383746, 32359054, 17673944, 12418600, 4235144, 14018717, 398320, 29150131,
      25080863, 4932463, 7459353, 5197824, 5546695, 20555201, 6354386, 18572737,
      4800262, 21493747, 6834421, 8310068, 2889493, 17892039, 4077813, 15782424],
    #[27240252, 10244421, 6702153, 15329239, 6337717, 15486594, 20216726, 30092453,
      19028797, 17718810, 24051397, 5255168, 19646324, 25064064, 1711427, 21148288,
      5332468, 3567771, 4902255, 24203247, 18569783, 513908, 2391407, 13685048],
    #[9057767, 29537597, 20058575, 8934326, 17441105, 12889531, 18100341, 31595105,
      20153828, 21925320, 20794244, 3375104, 24665131, 3420491, 25116865, 8339787,
      24663392, 19381376, 2496992, 19339435, 2223338, 3378219, 4970976, 11961105],
    #[29000071, 14505667, 2290127, 27789270, 18203311, 12851643, 1529560, 13769217,
      17379543, 7485595, 2411642, 2469888, 22202648, 1340747, 23753228, 7988555,
      4490323, 20421760, 2758867, 2981272, 3037972, 1042712, 7411923, 12337730],
    #[10521788, 12925318, 18429296, 29002827, 20378777, 26685101, 19586121, 30158841,
      588864, 20354176, 4078637, 7131136, 2335024, 20087501, 6978308, 22966989,
      22940669, 17458865, 23514444, 19525505, 21912116, 18493744, 22506828, 9582794],
    #[27917472, 16517953, 18316579, 12155585, 4085872, 29804649, 2042319, 26763673,
      4254782, 21720753, 23955746, 3915776, 3270941, 17038966, 3504388, 24841846,
      20463467, 5607513, 3465010, 19349828, 2596889, 23771421, 3125042, 8809357],
    #[28437648, 12270645, 20359456, 11601270, 4764369, 8524816, 18636144, 14708610,
      2758369, 5998681, 24498467, 4288512, 21133249, 17327913, 811264, 17311529,
      17180904, 5223681, 18951657, 5044928, 21034689, 7010241, 17141225, 25667002],
    #[28437648, 25713400, 2791539, 25322427, 5153489, 8651792, 420931, 14708610,
      19580545, 7917204, 23408931, 5345280, 22959858, 3330586, 3563571, 1221146,
      17194216, 21411487, 2660983, 23660653, 23516865, 5695218, 3816055, 25428759],
    #[26977665, 25532822, 8384034, 25796265, 7646790, 13112526, 22094029, 29580727,
      2537800, 21636233, 22820574, 1605632, 6422378, 18022966, 4683234, 21615158,
      16921948, 21523062, 5480234, 7064860, 1948296, 17362794, 667434, 26709703],
    #[25450015, 26271579, 24379249, 10427049, 21891861, 30926672, 4510208, 29567415,
      2808859, 7950884, 21419917, 565248, 21085034, 17389413, 21264175, 21329765,
      586767, 21290821, 24501066, 21097519, 588869, 547690, 17603402, 26085689],
    #[30499641, 30466553, 6873818, 15328923, 22566345, 32964358, 7845892, 14749101,
      19872305, 2284329, 18004548, 6684672, 22888683, 2244838, 24885796, 6971622,
      4130829, 6783687, 22469322, 18147884, 24107727, 2318571, 24283850, 16696556],
    #[10652472, 11733496, 8053466, 16508570, 20493769, 13039367, 3651588, 12586412,
      3945009, 5495593, 4373060, 6684672, 6045931, 19087590, 19577380, 23814374,
      4130829, 24609479, 21418698, 17164844, 4184783, 19030251, 6458058, 33539309],
    #[8858392, 28445144, 6732506, 14151354, 20493769, 31696679, 17741828, 13131148,
      20515377, 7828265, 22010436, 23463936, 21309675, 3090662, 18315812, 6752486,
      19531789, 8266439, 22706890, 18164268, 1798863, 20644075, 8266442, 13259981],
    #[31014711, 10204787, 21628785, 33108865, 18975509, 29527672, 17498624, 30705823,
      2792475, 6941220, 20084621, 17344512, 24642410, 24158053, 23844655, 20758373,
      21529615, 18644805, 23923530, 18938927, 18801733, 20048746, 1327946, 12437521],
    #[14440954, 28612077, 6694434, 12788434, 1830470, 15145141, 3023053, 33073612,
      444744, 21675145, 17725150, 18384896, 5785450, 23726646, 7927266, 19978806,
      4359516, 17828470, 4935466, 662812, 18580104, 3235690, 18020138, 12458684]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part09 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false),
  (13, false), (12, false), (13, false), (12, false),
  (0, false), (5, false), (12, true), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part09.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_144 :
    generatedNinthLowerSpinSourceQReplayWord 6 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 0)
    3456 24 0 (prefix_sizes 0) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_145 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3480 3504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_145 :
    generatedNinthLowerSpinSourceQReplayWord 6 145 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 1)
    3480 24 0 (prefix_sizes 1) slice_145
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_146 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3504 3528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_146 :
    generatedNinthLowerSpinSourceQReplayWord 6 146 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 2)
    3504 24 0 (prefix_sizes 2) slice_146
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_147 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3528 3552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_147 :
    generatedNinthLowerSpinSourceQReplayWord 6 147 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 3)
    3528 24 0 (prefix_sizes 3) slice_147
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_148 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3552 3576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_148 :
    generatedNinthLowerSpinSourceQReplayWord 6 148 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 4)
    3552 24 0 (prefix_sizes 4) slice_148
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_149 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3576 3600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_149 :
    generatedNinthLowerSpinSourceQReplayWord 6 149 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 5)
    3576 24 0 (prefix_sizes 5) slice_149
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_150 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3600 3624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_150 :
    generatedNinthLowerSpinSourceQReplayWord 6 150 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 6)
    3600 24 0 (prefix_sizes 6) slice_150
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_151 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3624 3648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_151 :
    generatedNinthLowerSpinSourceQReplayWord 6 151 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 7)
    3624 24 0 (prefix_sizes 7) slice_151
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_152 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3648 3672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_152 :
    generatedNinthLowerSpinSourceQReplayWord 6 152 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 8)
    3648 24 0 (prefix_sizes 8) slice_152
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_153 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3672 3696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_153 :
    generatedNinthLowerSpinSourceQReplayWord 6 153 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 9)
    3672 24 0 (prefix_sizes 9) slice_153
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_154 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3696 3720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_154 :
    generatedNinthLowerSpinSourceQReplayWord 6 154 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 10)
    3696 24 0 (prefix_sizes 10) slice_154
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_155 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3720 3744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_155 :
    generatedNinthLowerSpinSourceQReplayWord 6 155 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 11)
    3720 24 0 (prefix_sizes 11) slice_155
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_156 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3744 3768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_156 :
    generatedNinthLowerSpinSourceQReplayWord 6 156 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 12)
    3744 24 0 (prefix_sizes 12) slice_156
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_157 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3768 3792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_157 :
    generatedNinthLowerSpinSourceQReplayWord 6 157 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 13)
    3768 24 0 (prefix_sizes 13) slice_157
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_158 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3792 3816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_158 :
    generatedNinthLowerSpinSourceQReplayWord 6 158 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 14)
    3792 24 0 (prefix_sizes 14) slice_158
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_159 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3816 3840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_159 :
    generatedNinthLowerSpinSourceQReplayWord 6 159 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 15)
    3816 24 0 (prefix_sizes 15) slice_159
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_09_160 :
    generatedNinthLowerSpinSourceQReplayWord 6 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part09 16)
    3840 24 0 (prefix_sizes 16) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 144 160 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part09 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_09 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨144 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part09.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part09
    144 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (144 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
