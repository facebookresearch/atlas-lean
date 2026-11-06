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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 : Fin 17 → Array ℕ :=
  ![
    #[16699326, 13949491, 21037935, 26438900, 7670014, 9272103, 659470, 15387934,
      7028823, 1162936, 19830031, 21673984, 21336888, 23259702, 3208975, 23235126,
      18903310, 24697993, 916871, 24616881, 3978295, 21781304, 3517831, 33102193],
    #[27578501, 30342421, 2747823, 11499010, 21874782, 8712746, 17235982, 11065699,
      23836351, 21234319, 22089815, 22927360, 6679312, 5323290, 6343007, 6416922,
      8046858, 5449364, 22769566, 6016388, 23732815, 4252432, 23551902, 30359698],
    #[33311686, 26852962, 19908793, 13634644, 19470512, 31235873, 4456462, 9235879,
      22097038, 19695808, 1349311, 24012800, 7177271, 22816573, 16919739, 24966973,
      19970826, 3811240, 22785186, 1643423, 23201932, 2571319, 18570402, 11674108],
    #[15392678, 8740689, 1736308, 15751220, 18421968, 32550418, 23978992, 11299239,
      22998896, 19564704, 2835777, 24029184, 7459076, 5301774, 1997192, 6297102,
      7946, 1269814, 23248700, 3989810, 4466828, 895236, 16957244, 25747663],
    #[31485594, 28293371, 23917607, 28293149, 23351743, 15062980, 4623254, 8515229,
      2280743, 18279278, 2558927, 23255040, 6387968, 4456436, 6576975, 45044,
      2129652, 6390547, 4234727, 2193939, 6476367, 256, 1002983, 10941820],
    #[10704007, 29572449, 4323360, 9697229, 5361569, 13606005, 1798261, 26972536,
      17104940, 22940135, 2336116, 24954880, 5507084, 6380900, 2190395, 7695716,
      21331304, 19429323, 24709795, 1347527, 21206071, 49164, 16779939, 9559587],
    #[26198484, 14421759, 5310528, 28305150, 23842450, 30026456, 20457176, 10609739,
      1302604, 7884167, 19464263, 21628928, 23201804, 24971351, 2820360, 25102423,
      5232731, 19730694, 21023069, 465162, 23052548, 16777228, 20515165, 25751005],
    #[16720063, 28638103, 109504, 28662890, 23547531, 28668855, 7736393, 26395329,
      16875712, 23888706, 7202367, 20977664, 8182528, 23416079, 1163776, 23481615,
      5647887, 5622286, 9217, 23724302, 19507456, 3146496, 869377, 27912880],
    #[30048173, 29503368, 4360839, 15302429, 19548234, 26017193, 18127311, 26926454,
      21088911, 7178438, 19896600, 20973568, 21692424, 17825793, 919556, 22151169,
      7800841, 17367050, 198659, 4194306, 19335180, 24119304, 5441539, 29458522],
    #[10848357, 28931253, 2903220, 15226939, 21570242, 27777389, 3624304, 13192993,
      2602680, 18204813, 4251952, 21960704, 22993420, 24137725, 2670860, 20733949,
      6970865, 2283778, 20112627, 8323854, 3853056, 18915852, 21841139, 16198130],
    #[10940104, 11285112, 3856596, 15916296, 6620049, 28236531, 18578499, 15945234,
      20246549, 2542112, 22810723, 25151488, 7194817, 6991534, 19136575, 1081006,
      23416431, 2558927, 17753504, 22008590, 3397886, 3358913, 24216992, 16001855],
    #[12478329, 26126553, 24533171, 11298302, 24096138, 13127529, 7045325, 31188932,
      1795521, 17996325, 22918418, 21391360, 1891698, 5940378, 17942242, 1758362,
      4821480, 2336116, 17507484, 20539398, 24275856, 869746, 19350684, 30602986],
    #[11850282, 25890324, 8161664, 28923699, 7134023, 15870522, 21524992, 32677978,
      1353279, 2293285, 7903199, 21407744, 2695103, 24376164, 20789201, 20136804,
      4531419, 19464263, 914588, 397304, 22775918, 2664383, 3646620, 14193625],
    #[16661287, 14773702, 287043, 32651796, 6002231, 28704791, 22657028, 13003250,
      17549592, 20532010, 21227962, 23992320, 5085275, 24647909, 24111540, 22157541,
      3946686, 7202367, 7282305, 6581860, 16867823, 6914139, 4804225, 10740806],
    #[11850282, 25890324, 8161664, 28923699, 7134023, 15870522, 21524992, 32677978,
      1353279, 2293285, 7903199, 21407744, 2695103, 24376164, 20789201, 20136804,
      4531419, 19464263, 914588, 397304, 22775918, 2664383, 3646620, 14193625],
    #[12478329, 26126553, 24533171, 11298302, 24096138, 13127529, 7045325, 31188932,
      1795521, 17996325, 22918418, 21391360, 1891698, 5940378, 17942242, 1758362,
      4821480, 2336116, 17507484, 20539398, 24275856, 869746, 19350684, 30602986],
    #[10940104, 11285112, 3856596, 15916296, 6620049, 28236531, 18578499, 15945234,
      20246549, 2542112, 22810723, 25151488, 7194817, 6991534, 19136575, 1081006,
      23416431, 2558927, 17753504, 22008590, 3397886, 3358913, 24216992, 16001855]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part09 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part09.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_144 :
    generatedNinthLowerSpinSourceQReplayWord 5 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 0)
    3456 24 0 (prefix_sizes 0) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_145 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3480 3504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_145 :
    generatedNinthLowerSpinSourceQReplayWord 5 145 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 1)
    3480 24 0 (prefix_sizes 1) slice_145
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_146 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3504 3528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_146 :
    generatedNinthLowerSpinSourceQReplayWord 5 146 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 2)
    3504 24 0 (prefix_sizes 2) slice_146
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_147 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3528 3552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_147 :
    generatedNinthLowerSpinSourceQReplayWord 5 147 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 3)
    3528 24 0 (prefix_sizes 3) slice_147
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_148 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3552 3576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_148 :
    generatedNinthLowerSpinSourceQReplayWord 5 148 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 4)
    3552 24 0 (prefix_sizes 4) slice_148
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_149 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3576 3600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_149 :
    generatedNinthLowerSpinSourceQReplayWord 5 149 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 5)
    3576 24 0 (prefix_sizes 5) slice_149
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_150 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3600 3624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_150 :
    generatedNinthLowerSpinSourceQReplayWord 5 150 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 6)
    3600 24 0 (prefix_sizes 6) slice_150
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_151 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3624 3648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_151 :
    generatedNinthLowerSpinSourceQReplayWord 5 151 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 7)
    3624 24 0 (prefix_sizes 7) slice_151
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_152 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3648 3672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_152 :
    generatedNinthLowerSpinSourceQReplayWord 5 152 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 8)
    3648 24 0 (prefix_sizes 8) slice_152
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_153 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3672 3696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_153 :
    generatedNinthLowerSpinSourceQReplayWord 5 153 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 9)
    3672 24 0 (prefix_sizes 9) slice_153
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_154 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3696 3720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_154 :
    generatedNinthLowerSpinSourceQReplayWord 5 154 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 10)
    3696 24 0 (prefix_sizes 10) slice_154
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_155 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3720 3744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_155 :
    generatedNinthLowerSpinSourceQReplayWord 5 155 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 11)
    3720 24 0 (prefix_sizes 11) slice_155
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_156 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3744 3768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_156 :
    generatedNinthLowerSpinSourceQReplayWord 5 156 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 12)
    3744 24 0 (prefix_sizes 12) slice_156
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_157 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3768 3792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_157 :
    generatedNinthLowerSpinSourceQReplayWord 5 157 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 13)
    3768 24 0 (prefix_sizes 13) slice_157
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_158 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3792 3816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_158 :
    generatedNinthLowerSpinSourceQReplayWord 5 158 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 14)
    3792 24 0 (prefix_sizes 14) slice_158
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_159 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3816 3840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_159 :
    generatedNinthLowerSpinSourceQReplayWord 5 159 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 15)
    3816 24 0 (prefix_sizes 15) slice_159
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_09_160 :
    generatedNinthLowerSpinSourceQReplayWord 5 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part09 16)
    3840 24 0 (prefix_sizes 16) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 144 160 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part09 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_09 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨144 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part09.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part09
    144 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (144 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
