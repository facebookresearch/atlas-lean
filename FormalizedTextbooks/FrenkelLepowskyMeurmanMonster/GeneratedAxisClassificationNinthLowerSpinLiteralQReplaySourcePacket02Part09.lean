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
def generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 : Fin 17 → Array ℕ :=
  ![
    #[31633896, 13795672, 23835267, 14856683, 5931095, 13729468, 3329392, 30539352,
      22262584, 7866426, 22656047, 16992256, 6531515, 23575681, 6043968, 17902721,
      2620730, 948347, 8207681, 1573312, 6963451, 176571, 2788673, 28328237],
    #[33043675, 13112331, 24396061, 32650635, 23520612, 12733457, 17353795, 29522165,
      21636262, 23547812, 5481756, 19228672, 6495675, 24288812, 7784467, 18148908,
      289687, 17042728, 23207615, 19136659, 5698984, 181691, 17137343, 25772755],
    #[28936382, 14430465, 7237569, 28723266, 968479, 10142515, 8134861, 28769647,
      23867026, 21794196, 22587330, 22857728, 19069267, 17620699, 21268419, 22159067,
      7057288, 3223519, 4999255, 1169036, 19422864, 18624851, 6068311, 12733768],
    #[25594656, 31666847, 6586098, 9014236, 3872178, 12186110, 23056896, 27270415,
      6700961, 5687463, 22591394, 21641216, 16959827, 1280293, 21447950, 5081381,
      21117046, 2415890, 22027620, 20063297, 748637, 18624851, 23133540, 15255579],
    #[29063721, 14126472, 18724714, 12413623, 5137570, 25248668, 17369092, 32563201,
      7908197, 2399889, 22417302, 17577984, 4989967, 22189276, 5453820, 23737564,
      7932115, 7851980, 433951, 17791939, 23802867, 4766735, 4906783, 30617039],
    #[14868436, 11173041, 6696725, 26158501, 6150046, 28402039, 19054860, 33325053,
      7327512, 21467768, 145291, 17311744, 526349, 24952129, 20000616, 19582273,
      22314316, 18034297, 22182709, 21329524, 21854053, 6692877, 21977909, 11033230],
    #[33199941, 27598941, 18309687, 31834733, 19129735, 10661666, 787212, 14612629,
      5680842, 5941465, 20332614, 21968896, 24966397, 18973647, 20239387, 21967823,
      6471474, 21506266, 22028264, 1399847, 6709478, 20389117, 19308520, 33319237],
    #[12131015, 8772621, 2737386, 15707416, 3615554, 25190105, 3439368, 15897742,
      22606967, 1270862, 17668546, 17119232, 17328285, 21077364, 5800497, 19684724,
      21007849, 7932093, 6348116, 18452512, 16849580, 24461469, 8228180, 12668221],
    #[25210169, 8834720, 18244372, 13830187, 2612002, 11987673, 19741942, 31160176,
      5407012, 19560400, 17324911, 18024448, 2972208, 6146119, 5157425, 444487,
      21625463, 7142000, 5015559, 17408064, 18016257, 6730288, 4712455, 16289475],
    #[30380869, 11036084, 19363383, 13796134, 17605925, 10320752, 1869580, 32815303,
      5127971, 23046185, 1971631, 21985280, 24191252, 20136580, 20223003, 24654468,
      25000848, 7290257, 4726273, 1711237, 21918991, 18811156, 4120065, 30636311],
    #[12962694, 14797699, 21375815, 13211429, 21530238, 10187925, 18322782, 14954061,
      24038520, 4887080, 17375417, 24172544, 17915711, 19419073, 21618536, 18124737,
      3393790, 4905131, 104533, 1546132, 20877399, 18204479, 6572117, 30403390],
    #[31678342, 29636910, 7560586, 29569558, 22308685, 26743352, 17082355, 31780429,
      21907576, 21963909, 20747892, 24123392, 17083890, 16953074, 7764118, 17329906,
      707328, 24542616, 20246168, 17301610, 3421540, 20329970, 24632984, 14621534],
    #[8555417, 15506733, 21119889, 30973501, 6046932, 31330836, 24442895, 27854288,
      17624985, 22400916, 19434435, 21022720, 22782984, 22963204, 1037308, 24732676,
      19777548, 2670244, 7577256, 1366700, 7555060, 21011464, 7585448, 28145852],
    #[9318090, 32734931, 5132994, 16678461, 4853940, 30229721, 4782428, 9766019,
      18905802, 5015658, 895246, 20973568, 22872072, 23986180, 3145730, 21561348,
      1771532, 18548745, 23463941, 2164737, 23724042, 22022152, 24512517, 9144540],
    #[21923533, 20139736, 5147333, 4087352, 4892862, 21880027, 17316191, 1389696,
      6345416, 17573991, 21868810, 2048, 6125568, 7256064, 3198976, 4831232,
      6012928, 22777856, 2512896, 6414336, 6989824, 1079296, 3561472, 30098647],
    #[3692936, 7144521, 23551098, 23594215, 19208272, 21172414, 16779023, 6532785,
      21579911, 16905246, 4200718, 2048, 2144256, 7194624, 24576, 6752256,
      958464, 18317312, 5433344, 7528448, 2807808, 6989824, 6445056, 10611646],
    #[19139771, 5128836, 6826884, 21119412, 20133936, 7004960, 17155490, 6532785,
      4406740, 2021344, 7588803, 2048, 34816, 5965824, 3174400, 6801408,
      3051520, 17276928, 4462592, 4464640, 849920, 4999168, 4503552, 26340318]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters02Part09 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (12, false), (12, false), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (13, true), (14, false), (12, false), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters02Part09.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_144 :
    generatedNinthLowerSpinSourceQReplayWord 2 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 0)
    3456 24 0 (prefix_sizes 0) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_145 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3480 3504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_145 :
    generatedNinthLowerSpinSourceQReplayWord 2 145 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 1)
    3480 24 0 (prefix_sizes 1) slice_145
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_146 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3504 3528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_146 :
    generatedNinthLowerSpinSourceQReplayWord 2 146 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 2)
    3504 24 0 (prefix_sizes 2) slice_146
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_147 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3528 3552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_147 :
    generatedNinthLowerSpinSourceQReplayWord 2 147 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 3)
    3528 24 0 (prefix_sizes 3) slice_147
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_148 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3552 3576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_148 :
    generatedNinthLowerSpinSourceQReplayWord 2 148 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 4)
    3552 24 0 (prefix_sizes 4) slice_148
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_149 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3576 3600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_149 :
    generatedNinthLowerSpinSourceQReplayWord 2 149 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 5)
    3576 24 0 (prefix_sizes 5) slice_149
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_150 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3600 3624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_150 :
    generatedNinthLowerSpinSourceQReplayWord 2 150 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 6)
    3600 24 0 (prefix_sizes 6) slice_150
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_151 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3624 3648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_151 :
    generatedNinthLowerSpinSourceQReplayWord 2 151 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 7)
    3624 24 0 (prefix_sizes 7) slice_151
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_152 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3648 3672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_152 :
    generatedNinthLowerSpinSourceQReplayWord 2 152 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 8)
    3648 24 0 (prefix_sizes 8) slice_152
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_153 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3672 3696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_153 :
    generatedNinthLowerSpinSourceQReplayWord 2 153 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 9)
    3672 24 0 (prefix_sizes 9) slice_153
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_154 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3696 3720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_154 :
    generatedNinthLowerSpinSourceQReplayWord 2 154 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 10)
    3696 24 0 (prefix_sizes 10) slice_154
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_155 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3720 3744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_155 :
    generatedNinthLowerSpinSourceQReplayWord 2 155 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 11)
    3720 24 0 (prefix_sizes 11) slice_155
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_156 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3744 3768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_156 :
    generatedNinthLowerSpinSourceQReplayWord 2 156 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 12)
    3744 24 0 (prefix_sizes 12) slice_156
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_157 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3768 3792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_157 :
    generatedNinthLowerSpinSourceQReplayWord 2 157 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 13)
    3768 24 0 (prefix_sizes 13) slice_157
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_158 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3792 3816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_158 :
    generatedNinthLowerSpinSourceQReplayWord 2 158 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 14)
    3792 24 0 (prefix_sizes 14) slice_158
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_159 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3816 3840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_159 :
    generatedNinthLowerSpinSourceQReplayWord 2 159 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 15)
    3816 24 0 (prefix_sizes 15) slice_159
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_09_160 :
    generatedNinthLowerSpinSourceQReplayWord 2 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part09 16)
    3840 24 0 (prefix_sizes 16) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords02.extract 144 160 =
      generatedNinthLowerSpinLiteralQReplayLetters02Part09 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_02_part_09 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 2 ⟨144 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters02Part09.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords02
    generatedNinthLowerSpinLiteralQReplayLetters02Part09
    144 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords02.getD (144 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
