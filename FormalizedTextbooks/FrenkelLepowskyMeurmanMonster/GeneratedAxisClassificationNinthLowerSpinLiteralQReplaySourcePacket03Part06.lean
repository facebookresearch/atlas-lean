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
def generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 : Fin 17 → Array ℕ :=
  ![
    #[10745552, 12936947, 23864688, 29664072, 18398665, 31345358, 4709449, 29436604,
      18047567, 22419424, 20843268, 24676352, 2008895, 8112267, 19602477, 5802123,
      19548084, 3432417, 8343637, 7420126, 23714578, 8183615, 18184277, 32800409],
    #[27599149, 15892747, 7287247, 13227913, 23474965, 26419530, 22669016, 30104797,
      22358156, 19376181, 1163788, 22427648, 18123075, 5370824, 19700858, 7123912,
      4670091, 20176186, 4904881, 4990073, 894265, 23785795, 16932785, 14910375],
    #[9048787, 32646507, 23667151, 13861594, 8169030, 8828903, 4874357, 14204432,
      7538828, 18013944, 1179841, 22476800, 18123075, 25060438, 330628, 21312598,
      22992149, 3566487, 22476418, 5194452, 2237127, 21627203, 2014850, 13690218],
    #[11356542, 29276917, 7275593, 27602801, 703185, 13123124, 60310, 31136097,
      23926217, 7937546, 19684675, 23091200, 22663552, 23793634, 5824197, 22364130,
      20330082, 23539455, 23605405, 6332287, 18423621, 21453184, 1362077, 28452858],
    #[31391123, 8668759, 24141528, 11513288, 4018288, 26971974, 17966064, 30289065,
      20003605, 20102996, 18728402, 24463360, 19535309, 4485435, 20722201, 4690235,
      21650678, 17041419, 17415421, 22592966, 1398740, 24415693, 2708733, 13762048],
    #[13114867, 29090217, 7600245, 28567707, 1798256, 10353446, 725006, 16472676,
      1801798, 2828490, 3684223, 22259712, 17114675, 6616379, 17598073, 7415099,
      23317256, 19422552, 20754000, 7015275, 835658, 21716531, 2905680, 32640205],
    #[31391123, 8668759, 24141528, 11513288, 4018288, 26971974, 17966064, 30289065,
      20003605, 20102996, 18728402, 24463360, 19535309, 4485435, 20722201, 4690235,
      21650678, 17041419, 17415421, 22592966, 1398740, 24415693, 2708733, 13762048],
    #[11356542, 29276917, 7275593, 27602801, 703185, 13123124, 60310, 31136097,
      23926217, 7937546, 19684675, 23091200, 22663552, 23793634, 5824197, 22364130,
      20330082, 23539455, 23605405, 6332287, 18423621, 21453184, 1362077, 28452858],
    #[9048787, 32646507, 23667151, 13861594, 8169030, 8828903, 4874357, 14204432,
      7538828, 18013944, 1179841, 22476800, 18123075, 25060438, 330628, 21312598,
      22992149, 3566487, 22476418, 5194452, 2237127, 21627203, 2014850, 13690218],
    #[27599149, 15892747, 7287247, 13227913, 23474965, 26419530, 22669016, 30104797,
      22358156, 19376181, 1163788, 22427648, 18123075, 5370824, 19700858, 7123912,
      4670091, 20176186, 4904881, 4990073, 894265, 23785795, 16932785, 14910375],
    #[10745552, 12936947, 23864688, 29664072, 18398665, 31345358, 4709449, 29436604,
      18047567, 22419424, 20843268, 24676352, 2008895, 8112267, 19602477, 5802123,
      19548084, 3432417, 8343637, 7420126, 23714578, 8183615, 18184277, 32800409],
    #[14202437, 11288727, 23989539, 15888836, 7299212, 16259717, 22411727, 9261914,
      1631287, 24387416, 22595844, 22697984, 264468, 3651504, 1509666, 6506416,
      3774116, 7211173, 5207553, 6594993, 8233014, 1229076, 21798401, 10754164],
    #[33432133, 26277316, 24706339, 30946455, 24076428, 13549285, 5634511, 29095738,
      3305732, 23955654, 23374903, 23894016, 961575, 20489262, 326543, 24814638,
      1703945, 7057000, 21591649, 21729871, 23345064, 3691559, 6073953, 8555636],
    #[10056322, 16267034, 21783920, 31044257, 1621449, 15437374, 21486665, 32829004,
      2384644, 7111490, 2705999, 22890496, 19670644, 24840315, 199108, 24643707,
      1611279, 17567480, 24137975, 25061516, 22237104, 21749364, 1718519, 13564619],
    #[32560335, 10039915, 5272015, 10298601, 6697749, 26490184, 5891800, 13387999,
      23816716, 24661383, 1097868, 20744192, 25115587, 24245144, 23034696, 24376216,
      6164571, 5598730, 23119441, 1365449, 22167691, 22328259, 5291601, 11957829],
    #[16434684, 10507765, 21381583, 28217924, 24946246, 27148315, 21651573, 29379052,
      22964417, 6162919, 17825932, 19576832, 6998286, 5133414, 22076630, 5923942,
      22328680, 21965625, 24573521, 1794615, 7271896, 6775054, 7773777, 27275845],
    #[30047238, 12589577, 1205321, 27717517, 17480401, 27884346, 16837526, 28990575,
      5543235, 1502062, 6864329, 22706176, 19337482, 19529726, 24685355, 23769086,
      792308, 22027807, 2253035, 23998229, 24570401, 25090314, 18004203, 13963906]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters03Part06 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (13, false),
  (12, true), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters03Part06.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_096 :
    generatedNinthLowerSpinSourceQReplayWord 3 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 0)
    2304 24 0 (prefix_sizes 0) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_097 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2328 2352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_097 :
    generatedNinthLowerSpinSourceQReplayWord 3 97 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 1)
    2328 24 0 (prefix_sizes 1) slice_097
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_098 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2352 2376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_098 :
    generatedNinthLowerSpinSourceQReplayWord 3 98 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 2)
    2352 24 0 (prefix_sizes 2) slice_098
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_099 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2376 2400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_099 :
    generatedNinthLowerSpinSourceQReplayWord 3 99 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 3)
    2376 24 0 (prefix_sizes 3) slice_099
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_100 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2400 2424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_100 :
    generatedNinthLowerSpinSourceQReplayWord 3 100 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 4)
    2400 24 0 (prefix_sizes 4) slice_100
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_101 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2424 2448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_101 :
    generatedNinthLowerSpinSourceQReplayWord 3 101 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 5)
    2424 24 0 (prefix_sizes 5) slice_101
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_102 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2448 2472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_102 :
    generatedNinthLowerSpinSourceQReplayWord 3 102 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 6)
    2448 24 0 (prefix_sizes 6) slice_102
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_103 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2472 2496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_103 :
    generatedNinthLowerSpinSourceQReplayWord 3 103 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 7)
    2472 24 0 (prefix_sizes 7) slice_103
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_104 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2496 2520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_104 :
    generatedNinthLowerSpinSourceQReplayWord 3 104 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 8)
    2496 24 0 (prefix_sizes 8) slice_104
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_105 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2520 2544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_105 :
    generatedNinthLowerSpinSourceQReplayWord 3 105 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 9)
    2520 24 0 (prefix_sizes 9) slice_105
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_106 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2544 2568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_106 :
    generatedNinthLowerSpinSourceQReplayWord 3 106 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 10)
    2544 24 0 (prefix_sizes 10) slice_106
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_107 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2568 2592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_107 :
    generatedNinthLowerSpinSourceQReplayWord 3 107 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 11)
    2568 24 0 (prefix_sizes 11) slice_107
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_108 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2592 2616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_108 :
    generatedNinthLowerSpinSourceQReplayWord 3 108 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 12)
    2592 24 0 (prefix_sizes 12) slice_108
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_109 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2616 2640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_109 :
    generatedNinthLowerSpinSourceQReplayWord 3 109 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 13)
    2616 24 0 (prefix_sizes 13) slice_109
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_110 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2640 2664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_110 :
    generatedNinthLowerSpinSourceQReplayWord 3 110 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 14)
    2640 24 0 (prefix_sizes 14) slice_110
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_111 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2664 2688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_111 :
    generatedNinthLowerSpinSourceQReplayWord 3 111 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 15)
    2664 24 0 (prefix_sizes 15) slice_111
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_06_112 :
    generatedNinthLowerSpinSourceQReplayWord 3 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part06 16)
    2688 24 0 (prefix_sizes 16) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords03.extract 96 112 =
      generatedNinthLowerSpinLiteralQReplayLetters03Part06 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_03_part_06 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 3 ⟨96 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters03Part06.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords03
    generatedNinthLowerSpinLiteralQReplayLetters03Part06
    96 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords03.getD (96 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
