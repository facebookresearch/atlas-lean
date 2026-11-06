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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 : Fin 17 → Array ℕ :=
  ![
    #[14440954, 28612077, 6694434, 12788434, 1830470, 15145141, 3023053, 33073612,
      444744, 21675145, 17725150, 18384896, 5785450, 23726646, 7927266, 19978806,
      4359516, 17828470, 4935466, 662812, 18580104, 3235690, 18020138, 12458684],
    #[25181018, 27159858, 4382835, 25318513, 3928785, 9720794, 21412931, 9658440,
      22525569, 2762388, 22262051, 22124544, 21716722, 8194586, 7229491, 6126106,
      6065384, 20911775, 780919, 17148013, 2879169, 21227250, 18432631, 13221085],
    #[9486138, 28159903, 22941984, 9545436, 2822865, 26404794, 7101808, 10814504,
      7440097, 2068569, 23290147, 21067776, 24207297, 24604457, 4501760, 24588073,
      4851944, 443649, 19168745, 3582656, 3870401, 22665153, 54761, 31215120],
    #[9287244, 29135277, 21890339, 29233197, 2828400, 28934789, 22411727, 28681077,
      5864510, 21853873, 20265250, 20695040, 7405853, 21177974, 1796356, 20698742,
      3673963, 2768985, 4931378, 18379076, 21583897, 2775325, 22038322, 16071009],
    #[32600287, 16082405, 19635568, 15130664, 21775513, 9282254, 4709449, 12594074,
      1207360, 20155520, 7179309, 23910400, 760112, 22579917, 7129860, 20216525,
      1850365, 23111345, 21904716, 23797633, 6345268, 3277104, 8361292, 9088169],
    #[11940214, 8881714, 8124879, 12535591, 21156527, 16017738, 22669016, 16311024,
      17932503, 7676059, 3239034, 19249152, 18043160, 1367371, 25145868, 7949643,
      17151059, 18300032, 4950227, 5000600, 24773396, 21920024, 17858771, 29702835],
    #[8738747, 25909089, 21752271, 9105898, 22933841, 29429735, 4874357, 33235005,
      17507812, 22656456, 20896644, 20154368, 20513835, 297291, 21799105, 5241163,
      636256, 18300032, 6781408, 22464683, 22238442, 24304683, 17478112, 30079309],
    #[25698186, 27003379, 4959305, 26693473, 644277, 31258164, 60310, 15469587,
      24927037, 21956122, 20848325, 22034432, 22556532, 24017536, 8060227, 22198912,
      20102644, 6570139, 8068463, 22061039, 545335, 24393588, 18195823, 25534862],
    #[26987161, 31468885, 23799512, 30630387, 7532424, 12248902, 17966064, 8539240,
      20497439, 3713903, 1348121, 21977088, 7625415, 24436161, 1013202, 22420929,
      19185414, 21739507, 624885, 5406004, 23293717, 3273415, 23064821, 11892163],
    #[26963705, 32082603, 6193269, 15958419, 5994614, 29135654, 725006, 8661096,
      136524, 19745218, 1324665, 23050240, 24849721, 6024767, 19699583, 5189183,
      2284294, 6837598, 1891928, 22546535, 6281798, 20469049, 23746136, 11892163],
    #[26987161, 31468885, 23799512, 30630387, 7532424, 12248902, 17966064, 8539240,
      20497439, 3713903, 1348121, 21977088, 7625415, 24436161, 1013202, 22420929,
      19185414, 21739507, 624885, 5406004, 23293717, 3273415, 23064821, 11892163],
    #[25698186, 27003379, 4959305, 26693473, 644277, 31258164, 60310, 15469587,
      24927037, 21956122, 20848325, 22034432, 22556532, 24017536, 8060227, 22198912,
      20102644, 6570139, 8068463, 22061039, 545335, 24393588, 18195823, 25534862],
    #[8738747, 25909089, 21752271, 9105898, 22933841, 29429735, 4874357, 33235005,
      17507812, 22656456, 20896644, 20154368, 20513835, 297291, 21799105, 5241163,
      636256, 18300032, 6781408, 22464683, 22238442, 24304683, 17478112, 30079309],
    #[11940214, 8881714, 8124879, 12535591, 21156527, 16017738, 22669016, 16311024,
      17932503, 7676059, 3239034, 19249152, 18043160, 1367371, 25145868, 7949643,
      17151059, 18300032, 4950227, 5000600, 24773396, 21920024, 17858771, 29702835],
    #[32600287, 16082405, 19635568, 15130664, 21775513, 9282254, 4709449, 12594074,
      1207360, 20155520, 7179309, 23910400, 760112, 22579917, 7129860, 20216525,
      1850365, 23111345, 21904716, 23797633, 6345268, 3277104, 8361292, 9088169],
    #[9287244, 29135277, 21890339, 29233197, 2828400, 28934789, 22411727, 28681077,
      5864510, 21853873, 20265250, 20695040, 7405853, 21177974, 1796356, 20698742,
      3673963, 2768985, 4931378, 18379076, 21583897, 2775325, 22038322, 16071009],
    #[8942817, 10728019, 24692003, 25891552, 2963568, 26207973, 5634511, 26867238,
      24551328, 21853873, 19987343, 19789824, 24691331, 21594949, 1166391, 16884549,
      18696646, 2750100, 5062482, 20243479, 21769908, 17136259, 23086930, 32115455]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part10 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part10.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_160 :
    generatedNinthLowerSpinSourceQReplayWord 6 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 0)
    3840 24 0 (prefix_sizes 0) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_161 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3864 3888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_161 :
    generatedNinthLowerSpinSourceQReplayWord 6 161 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 1)
    3864 24 0 (prefix_sizes 1) slice_161
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_162 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3888 3912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_162 :
    generatedNinthLowerSpinSourceQReplayWord 6 162 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 2)
    3888 24 0 (prefix_sizes 2) slice_162
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_163 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3912 3936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_163 :
    generatedNinthLowerSpinSourceQReplayWord 6 163 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 3)
    3912 24 0 (prefix_sizes 3) slice_163
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_164 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3936 3960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_164 :
    generatedNinthLowerSpinSourceQReplayWord 6 164 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 4)
    3936 24 0 (prefix_sizes 4) slice_164
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_165 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3960 3984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_165 :
    generatedNinthLowerSpinSourceQReplayWord 6 165 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 5)
    3960 24 0 (prefix_sizes 5) slice_165
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_166 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 3984 4008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_166 :
    generatedNinthLowerSpinSourceQReplayWord 6 166 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 6)
    3984 24 0 (prefix_sizes 6) slice_166
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (3984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_167 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4008 4032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_167 :
    generatedNinthLowerSpinSourceQReplayWord 6 167 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 7)
    4008 24 0 (prefix_sizes 7) slice_167
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_168 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4032 4056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_168 :
    generatedNinthLowerSpinSourceQReplayWord 6 168 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 8)
    4032 24 0 (prefix_sizes 8) slice_168
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_169 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4056 4080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_169 :
    generatedNinthLowerSpinSourceQReplayWord 6 169 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 9)
    4056 24 0 (prefix_sizes 9) slice_169
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_170 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4080 4104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_170 :
    generatedNinthLowerSpinSourceQReplayWord 6 170 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 10)
    4080 24 0 (prefix_sizes 10) slice_170
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_171 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4104 4128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_171 :
    generatedNinthLowerSpinSourceQReplayWord 6 171 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 11)
    4104 24 0 (prefix_sizes 11) slice_171
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_172 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4128 4152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_172 :
    generatedNinthLowerSpinSourceQReplayWord 6 172 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 12)
    4128 24 0 (prefix_sizes 12) slice_172
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_173 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4152 4176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_173 :
    generatedNinthLowerSpinSourceQReplayWord 6 173 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 13)
    4152 24 0 (prefix_sizes 13) slice_173
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_174 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4176 4200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_174 :
    generatedNinthLowerSpinSourceQReplayWord 6 174 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 14)
    4176 24 0 (prefix_sizes 14) slice_174
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_175 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4200 4224 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_175 :
    generatedNinthLowerSpinSourceQReplayWord 6 175 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 15)
    4200 24 0 (prefix_sizes 15) slice_175
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4200 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_176 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 4224 4248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_10_176 :
    generatedNinthLowerSpinSourceQReplayWord 6 176 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part10 16)
    4224 24 0 (prefix_sizes 16) slice_176
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (4224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 160 176 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_10 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨160 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part10.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part10
    160 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (160 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
