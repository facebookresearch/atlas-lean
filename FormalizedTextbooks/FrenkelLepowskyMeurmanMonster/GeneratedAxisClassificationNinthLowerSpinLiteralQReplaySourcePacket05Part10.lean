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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 : Fin 17 → Array ℕ :=
  ![
    #[10940104, 11285112, 3856596, 15916296, 6620049, 28236531, 18578499, 15945234,
      20246549, 2542112, 22810723, 25151488, 7194817, 6991534, 19136575, 1081006,
      23416431, 2558927, 17753504, 22008590, 3397886, 3358913, 24216992, 16001855],
    #[10848357, 28931253, 2903220, 15226939, 21570242, 27777389, 3624304, 13192993,
      2602680, 18204813, 4251952, 21960704, 22993420, 24137725, 2670860, 20733949,
      6970865, 2283778, 20112627, 8323854, 3853056, 18915852, 21841139, 16198130],
    #[30048173, 29503368, 4360839, 15302429, 19548234, 26017193, 18127311, 26926454,
      21088911, 7178438, 19896600, 20973568, 21692424, 17825793, 919556, 22151169,
      7800841, 17367050, 198659, 4194306, 19335180, 24119304, 5441539, 29458522],
    #[16720063, 28638103, 109504, 28662890, 23547531, 28668855, 7736393, 26395329,
      16875712, 23888706, 7202367, 20977664, 8182528, 23416079, 1163776, 23481615,
      5647887, 5622286, 9217, 23724302, 19507456, 3146496, 869377, 27912880],
    #[26198484, 14421759, 5310528, 28305150, 23842450, 30026456, 20457176, 10609739,
      1302604, 7884167, 19464263, 21628928, 23201804, 24971351, 2820360, 25102423,
      5232731, 19730694, 21023069, 465162, 23052548, 16777228, 20515165, 25751005],
    #[10704007, 29572449, 4323360, 9697229, 5361569, 13606005, 1798261, 26972536,
      17104940, 22940135, 2336116, 24954880, 5507084, 6380900, 2190395, 7695716,
      21331304, 19429323, 24709795, 1347527, 21206071, 49164, 16779939, 9559587],
    #[31485594, 28293371, 23917607, 28293149, 23351743, 15062980, 4623254, 8515229,
      2280743, 18279278, 2558927, 23255040, 6387968, 4456436, 6576975, 45044,
      2129652, 6390547, 4234727, 2193939, 6476367, 256, 1002983, 10941820],
    #[15392678, 8740689, 1736308, 15751220, 18421968, 32550418, 23978992, 11299239,
      22998896, 19564704, 2835777, 24029184, 7459076, 5301774, 1997192, 6297102,
      7946, 1269814, 23248700, 3989810, 4466828, 895236, 16957244, 25747663],
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
    #[29802142, 31172726, 23977241, 30649934, 249812, 26438231, 3434959, 27245499,
      21547281, 7610200, 20171819, 21022720, 23958536, 385708, 2006020, 5313196,
      6446756, 20359156, 989520, 21955580, 2607116, 21015560, 5241168, 30336964],
    #[30582182, 8683415, 2031458, 26675665, 22874665, 8447927, 22252617, 9081816,
      17059888, 5642208, 25110388, 23074816, 21389138, 21514470, 19826258, 23791846,
      21053364, 23453198, 17281466, 6345052, 633088, 17483602, 19890618, 11746834]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part10 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, true), (12, true), (13, true),
  (13, false), (12, false), (12, false), (13, false),
  (12, false), (12, false), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part10.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_160 :
    generatedNinthLowerSpinSourceQReplayWord 5 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 0)
    3840 24 0 (prefix_sizes 0) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_161 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3864 3888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_161 :
    generatedNinthLowerSpinSourceQReplayWord 5 161 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 1)
    3864 24 0 (prefix_sizes 1) slice_161
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_162 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3888 3912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_162 :
    generatedNinthLowerSpinSourceQReplayWord 5 162 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 2)
    3888 24 0 (prefix_sizes 2) slice_162
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_163 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3912 3936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_163 :
    generatedNinthLowerSpinSourceQReplayWord 5 163 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 3)
    3912 24 0 (prefix_sizes 3) slice_163
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_164 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3936 3960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_164 :
    generatedNinthLowerSpinSourceQReplayWord 5 164 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 4)
    3936 24 0 (prefix_sizes 4) slice_164
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_165 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3960 3984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_165 :
    generatedNinthLowerSpinSourceQReplayWord 5 165 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 5)
    3960 24 0 (prefix_sizes 5) slice_165
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_166 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 3984 4008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_166 :
    generatedNinthLowerSpinSourceQReplayWord 5 166 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 6)
    3984 24 0 (prefix_sizes 6) slice_166
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (3984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_167 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4008 4032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_167 :
    generatedNinthLowerSpinSourceQReplayWord 5 167 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 7)
    4008 24 0 (prefix_sizes 7) slice_167
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_168 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4032 4056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_168 :
    generatedNinthLowerSpinSourceQReplayWord 5 168 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 8)
    4032 24 0 (prefix_sizes 8) slice_168
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_169 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4056 4080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_169 :
    generatedNinthLowerSpinSourceQReplayWord 5 169 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 9)
    4056 24 0 (prefix_sizes 9) slice_169
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_170 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4080 4104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_170 :
    generatedNinthLowerSpinSourceQReplayWord 5 170 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 10)
    4080 24 0 (prefix_sizes 10) slice_170
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_171 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4104 4128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_171 :
    generatedNinthLowerSpinSourceQReplayWord 5 171 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 11)
    4104 24 0 (prefix_sizes 11) slice_171
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_172 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4128 4152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_172 :
    generatedNinthLowerSpinSourceQReplayWord 5 172 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 12)
    4128 24 0 (prefix_sizes 12) slice_172
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_173 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4152 4176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_173 :
    generatedNinthLowerSpinSourceQReplayWord 5 173 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 13)
    4152 24 0 (prefix_sizes 13) slice_173
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_174 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4176 4200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_174 :
    generatedNinthLowerSpinSourceQReplayWord 5 174 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 14)
    4176 24 0 (prefix_sizes 14) slice_174
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_175 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4200 4224 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_175 :
    generatedNinthLowerSpinSourceQReplayWord 5 175 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 15)
    4200 24 0 (prefix_sizes 15) slice_175
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4200 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_176 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4224 4248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_10_176 :
    generatedNinthLowerSpinSourceQReplayWord 5 176 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part10 16)
    4224 24 0 (prefix_sizes 16) slice_176
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 160 176 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_10 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨160 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part10.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part10
    160 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (160 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
