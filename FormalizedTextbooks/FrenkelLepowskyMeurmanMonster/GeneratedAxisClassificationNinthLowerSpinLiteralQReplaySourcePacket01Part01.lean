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
def generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 : Fin 17 → Array ℕ :=
  ![
    #[7882445, 7177944, 3705541, 4691512, 6791358, 18226395, 17316191, 17104000,
      1497800, 24780903, 504074, 2048, 6123520, 7254016, 3198976, 4829184,
      6012928, 22779904, 2510848, 6414336, 6987776, 1077248, 3559424, 30428379],
    #[28847814, 11370207, 7887554, 8879665, 19339444, 30821589, 4782428, 29625487,
      5667530, 20613226, 17277198, 20973568, 1902600, 3016708, 3145730, 591876,
      1771532, 5963785, 2490373, 2164737, 2754570, 1048584, 3538949, 13648080],
    #[28593045, 11705633, 24398737, 10591793, 17272020, 32758296, 24442895, 33033692,
      8007577, 2297748, 1344451, 21022720, 1797128, 2010116, 1037308, 3779588,
      19777548, 23623332, 20141736, 1366700, 20156404, 21512, 20149928, 12628144],
    #[26684550, 30186030, 533898, 12669206, 5951309, 26401080, 17082355, 32130381,
      4532344, 4473989, 4779636, 24123392, 7648754, 7517938, 7764118, 7894770,
      707328, 419224, 4519576, 17301610, 21245284, 4599282, 509592, 10141790],
    #[27806584, 32918397, 19637063, 14866395, 6692478, 11058283, 18322782, 29734579,
      7576696, 22528552, 7055545, 24172544, 6391615, 5806017, 21618536, 6576065,
      3393790, 20578475, 24199253, 1546132, 5130327, 6627135, 18124885, 25420736],
    #[27029717, 25945636, 21274167, 28995766, 7163173, 31457504, 1869580, 27480919,
      23244579, 7551017, 24903087, 21985280, 4086036, 8141444, 20223003, 3623556,
      25000848, 18892177, 17262081, 1711237, 68879, 5271828, 24225281, 32006791],
    #[11059022, 8699095, 23563028, 9075292, 22360866, 33493166, 19741942, 12283143,
      19947812, 4757456, 3322735, 18024448, 20861488, 21938247, 5157425, 18202695,
      21625463, 25162352, 23035911, 17408064, 122881, 24492592, 22339591, 31483060],
    #[28872494, 8915428, 6880490, 26196209, 24314690, 12636976, 3439368, 26999143,
      1897591, 22504526, 2179522, 17119232, 872605, 4498804, 5800497, 2712948,
      21007849, 24916157, 23455060, 18452512, 271020, 7370909, 24687956, 31457492],
    #[9646199, 12351343, 22305335, 26355039, 6802823, 12587024, 787212, 26662823,
      22720202, 22456537, 5498950, 21968896, 3394813, 7257039, 20239387, 3023,
      6471474, 463066, 2041832, 1399847, 19486950, 7873789, 6924264, 16279159],
    #[33204888, 10152445, 6686485, 15319273, 18481054, 31792187, 19054860, 28988081,
      23580440, 5214840, 18370443, 17311744, 16785421, 7640385, 20000616, 2286913,
      22314316, 1771129, 5919541, 21329524, 4546405, 23988237, 4682549, 32393154],
    #[9071354, 9248091, 22388586, 31414884, 17452194, 33049423, 17369092, 32860370,
      20757349, 23105169, 2537366, 17577984, 20978703, 6204636, 5453820, 6687964,
      7932115, 24901580, 17475359, 17791939, 6753267, 21267471, 21423903, 9737500],
    #[30059350, 28725993, 2643698, 25357226, 25116082, 33278344, 23056896, 33031545,
      23080865, 22075559, 569250, 21641216, 4780371, 22655269, 21447950, 17281317,
      21117046, 24044818, 1713508, 20063297, 21058653, 5638483, 2803044, 32628845],
    #[16518966, 25228937, 3454913, 11816906, 24915743, 15822011, 8134861, 32600807,
      6962834, 4890004, 2641858, 22857728, 8270163, 5248731, 21268419, 972507,
      7057288, 23979999, 17858647, 1169036, 7640720, 4258131, 16797783, 15999680],
    #[28890956, 12089244, 22296861, 14951964, 462180, 12986246, 17353795, 29459298,
      5190822, 6447012, 24206620, 19228672, 21394875, 5764652, 7784467, 3245612,
      289687, 2188584, 4683455, 19136659, 24354216, 19377595, 2102975, 32069956],
    #[8852690, 9929826, 23853699, 30483665, 18585687, 32932742, 3329392, 29459298,
      5288760, 24840250, 7175215, 16992256, 23126459, 6616193, 6043968, 1205377,
      2620730, 17641595, 25064769, 1573312, 23660795, 16906683, 19514689, 32840727],
    #[15456555, 33261054, 19071424, 27895082, 753343, 29898699, 21064143, 30667168,
      23968528, 22413842, 7949684, 24836096, 1381072, 2401684, 4537729, 3380628,
      1847108, 24517528, 20024540, 17746248, 8019793, 5880528, 23608540, 10155624],
    #[29092386, 31034632, 4331848, 9096063, 7767182, 11797267, 1334345, 12593642,
      22770743, 2806845, 4539343, 19916800, 4375935, 7133092, 1025168, 2983844,
      24271579, 20960254, 1847589, 1287809, 20386287, 1707391, 954661, 31454968]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters01Part01 : Array GeneratedNinthLowerSpinLetter := #[
  (14, true), (13, false), (12, false), (13, false),
  (12, false), (12, false), (13, false), (12, true),
  (12, true), (12, true), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters01Part01.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_016 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 384 408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_016 :
    generatedNinthLowerSpinSourceQReplayWord 1 16 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 0)
    384 24 0 (prefix_sizes 0) slice_016
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_017 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 408 432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_017 :
    generatedNinthLowerSpinSourceQReplayWord 1 17 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 1)
    408 24 0 (prefix_sizes 1) slice_017
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_018 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 432 456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_018 :
    generatedNinthLowerSpinSourceQReplayWord 1 18 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 2)
    432 24 0 (prefix_sizes 2) slice_018
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_019 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 456 480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_019 :
    generatedNinthLowerSpinSourceQReplayWord 1 19 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 3)
    456 24 0 (prefix_sizes 3) slice_019
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_020 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 480 504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_020 :
    generatedNinthLowerSpinSourceQReplayWord 1 20 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 4)
    480 24 0 (prefix_sizes 4) slice_020
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_021 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 504 528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_021 :
    generatedNinthLowerSpinSourceQReplayWord 1 21 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 5)
    504 24 0 (prefix_sizes 5) slice_021
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_022 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 528 552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_022 :
    generatedNinthLowerSpinSourceQReplayWord 1 22 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 6)
    528 24 0 (prefix_sizes 6) slice_022
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_023 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 552 576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_023 :
    generatedNinthLowerSpinSourceQReplayWord 1 23 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 7)
    552 24 0 (prefix_sizes 7) slice_023
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_024 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 576 600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_024 :
    generatedNinthLowerSpinSourceQReplayWord 1 24 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 8)
    576 24 0 (prefix_sizes 8) slice_024
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_025 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 600 624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_025 :
    generatedNinthLowerSpinSourceQReplayWord 1 25 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 9)
    600 24 0 (prefix_sizes 9) slice_025
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_026 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 624 648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_026 :
    generatedNinthLowerSpinSourceQReplayWord 1 26 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 10)
    624 24 0 (prefix_sizes 10) slice_026
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_027 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 648 672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_027 :
    generatedNinthLowerSpinSourceQReplayWord 1 27 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 11)
    648 24 0 (prefix_sizes 11) slice_027
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_028 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 672 696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_028 :
    generatedNinthLowerSpinSourceQReplayWord 1 28 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 12)
    672 24 0 (prefix_sizes 12) slice_028
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_029 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 696 720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_029 :
    generatedNinthLowerSpinSourceQReplayWord 1 29 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 13)
    696 24 0 (prefix_sizes 13) slice_029
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_030 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 720 744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_030 :
    generatedNinthLowerSpinSourceQReplayWord 1 30 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 14)
    720 24 0 (prefix_sizes 14) slice_030
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_031 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 744 768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_031 :
    generatedNinthLowerSpinSourceQReplayWord 1 31 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 15)
    744 24 0 (prefix_sizes 15) slice_031
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_032 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 768 792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_01_032 :
    generatedNinthLowerSpinSourceQReplayWord 1 32 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part01 16)
    768 24 0 (prefix_sizes 16) slice_032
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords01.extract 16 32 =
      generatedNinthLowerSpinLiteralQReplayLetters01Part01 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_01_part_01 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 1 ⟨16 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters01Part01.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords01
    generatedNinthLowerSpinLiteralQReplayLetters01Part01
    16 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords01.getD (16 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
