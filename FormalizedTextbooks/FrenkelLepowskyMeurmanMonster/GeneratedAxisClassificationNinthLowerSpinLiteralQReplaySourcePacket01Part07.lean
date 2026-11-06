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
def generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 : Fin 17 → Array ℕ :=
  ![
    #[14314643, 10398920, 5310168, 10213207, 17307760, 32969169, 1188848, 25852478,
      17401298, 311456, 19718933, 19965952, 7740170, 19954688, 23323434, 16813056,
      6770442, 1465440, 4195178, 23074666, 2467872, 6189834, 23124842, 32829184],
    #[32935360, 11458728, 24285301, 11039130, 17307760, 33423919, 17502222, 28339053,
      3819391, 1237184, 3188294, 19965952, 21397258, 16804864, 7714634, 18922496,
      21433098, 1465440, 24143722, 4215658, 2336832, 22939402, 4235114, 16596222],
    #[14314643, 10398920, 5310168, 10213207, 17307760, 32969169, 1188848, 25852478,
      17401298, 311456, 19718933, 19965952, 7740170, 19954688, 23323434, 16813056,
      6770442, 1465440, 4195178, 23074666, 2467872, 6189834, 23124842, 32829184],
    #[29600114, 30711677, 20442185, 11463417, 19264209, 26437198, 16837526, 11766043,
      21159235, 4658030, 23641545, 22706176, 18143498, 23769086, 7908139, 19529726,
      8163060, 8107551, 7952619, 7753493, 4530721, 21827850, 21594347, 28588022],
    #[30339539, 12120538, 6732239, 15447659, 23879238, 31919156, 21651573, 32800195,
      3399873, 1278439, 1048716, 19576832, 2601230, 5923942, 5299414, 5133414,
      17694056, 7070521, 17530449, 24302135, 19107288, 2758926, 726609, 10810986],
    #[30933459, 28014455, 24152527, 30671349, 4643605, 31942740, 5891800, 31759811,
      1053196, 16975239, 17875084, 20744192, 19182531, 24376216, 6257480, 24245144,
      497755, 24622602, 18587217, 23954889, 641163, 17775555, 2877009, 12481369],
    #[11183424, 30568664, 4164976, 26711395, 6571465, 29409788, 21486665, 13056398,
      21961476, 4971330, 19483215, 22890496, 20233844, 24643707, 16976324, 24840315,
      200207, 4183800, 22550775, 5580940, 4970416, 22234740, 3305719, 30276873],
    #[15012914, 30430131, 3777827, 30032608, 19343500, 13570194, 5634511, 10535245,
      23705860, 25059526, 6597687, 23894016, 1324071, 24814638, 17103759, 20489262,
      4364297, 19514984, 22253153, 1270351, 8302504, 2280487, 4609633, 26860035],
    #[14626273, 31904933, 4288800, 27678890, 24052303, 14694769, 23879024, 30355249,
      17350912, 1785997, 7066384, 19789824, 17668128, 20733393, 19744436, 24137169,
      7671281, 7642135, 17691110, 18408503, 8195732, 17154080, 285158, 29502711],
    #[16129663, 32723560, 25014387, 10088244, 22413745, 16325359, 4635715, 30744066,
      19198003, 18371104, 24256750, 20695040, 19638336, 3382831, 2682905, 4804143,
      24780399, 5818692, 18396971, 20082948, 23611481, 18079808, 1122091, 30296484],
    #[27448024, 27069417, 21591586, 25741291, 8097711, 9301849, 19800269, 11928820,
      22210018, 4440613, 3166368, 21067776, 18598848, 24257064, 23058113, 20075048,
      6685160, 18653888, 1102632, 17197312, 21683457, 20022208, 20437800, 16704110],
    #[25662581, 11640506, 5588849, 9285958, 7900514, 11618922, 721408, 11972852,
      6809391, 23283237, 2121920, 22124544, 19060830, 23573637, 24770241, 19334277,
      5940443, 3772525, 18855094, 17459251, 4574879, 20877406, 3718326, 15868765],
    #[10152926, 29900454, 21379802, 12573134, 7578909, 32379111, 964612, 33450642,
      2054692, 5391146, 8141455, 18384896, 3393790, 1689664, 6830728, 3393600,
      2341054, 20071708, 241058, 20123106, 5272182, 5325054, 17393058, 28312581],
    #[25662581, 11640506, 5588849, 9285958, 7900514, 11618922, 721408, 11972852,
      6809391, 23283237, 2121920, 22124544, 19060830, 23573637, 24770241, 19334277,
      5940443, 3772525, 18855094, 17459251, 4574879, 20877406, 3718326, 15868765],
    #[27448024, 27069417, 21591586, 25741291, 8097711, 9301849, 19800269, 11928820,
      22210018, 4440613, 3166368, 21067776, 18598848, 24257064, 23058113, 20075048,
      6685160, 18653888, 1102632, 17197312, 21683457, 20022208, 20437800, 16704110],
    #[16129663, 32723560, 25014387, 10088244, 22413745, 16325359, 4635715, 30744066,
      19198003, 18371104, 24256750, 20695040, 19638336, 3382831, 2682905, 4804143,
      24780399, 5818692, 18396971, 20082948, 23611481, 18079808, 1122091, 30296484],
    #[14626273, 31904933, 4288800, 27678890, 24052303, 14694769, 23879024, 30355249,
      17350912, 1785997, 7066384, 19789824, 17668128, 20733393, 19744436, 24137169,
      7671281, 7642135, 17691110, 18408503, 8195732, 17154080, 285158, 29502711]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters01Part07 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false),
  (13, false), (12, false), (13, false), (12, false),
  (12, true), (13, true), (12, true), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters01Part07.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_112 :
    generatedNinthLowerSpinSourceQReplayWord 1 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 0)
    2688 24 0 (prefix_sizes 0) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_113 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2712 2736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_113 :
    generatedNinthLowerSpinSourceQReplayWord 1 113 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 1)
    2712 24 0 (prefix_sizes 1) slice_113
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_114 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2736 2760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_114 :
    generatedNinthLowerSpinSourceQReplayWord 1 114 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 2)
    2736 24 0 (prefix_sizes 2) slice_114
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_115 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2760 2784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_115 :
    generatedNinthLowerSpinSourceQReplayWord 1 115 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 3)
    2760 24 0 (prefix_sizes 3) slice_115
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_116 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2784 2808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_116 :
    generatedNinthLowerSpinSourceQReplayWord 1 116 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 4)
    2784 24 0 (prefix_sizes 4) slice_116
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_117 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2808 2832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_117 :
    generatedNinthLowerSpinSourceQReplayWord 1 117 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 5)
    2808 24 0 (prefix_sizes 5) slice_117
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_118 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2832 2856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_118 :
    generatedNinthLowerSpinSourceQReplayWord 1 118 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 6)
    2832 24 0 (prefix_sizes 6) slice_118
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_119 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2856 2880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_119 :
    generatedNinthLowerSpinSourceQReplayWord 1 119 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 7)
    2856 24 0 (prefix_sizes 7) slice_119
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_120 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2880 2904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_120 :
    generatedNinthLowerSpinSourceQReplayWord 1 120 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 8)
    2880 24 0 (prefix_sizes 8) slice_120
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_121 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2904 2928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_121 :
    generatedNinthLowerSpinSourceQReplayWord 1 121 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 9)
    2904 24 0 (prefix_sizes 9) slice_121
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_122 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2928 2952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_122 :
    generatedNinthLowerSpinSourceQReplayWord 1 122 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 10)
    2928 24 0 (prefix_sizes 10) slice_122
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_123 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2952 2976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_123 :
    generatedNinthLowerSpinSourceQReplayWord 1 123 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 11)
    2952 24 0 (prefix_sizes 11) slice_123
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_124 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 2976 3000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_124 :
    generatedNinthLowerSpinSourceQReplayWord 1 124 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 12)
    2976 24 0 (prefix_sizes 12) slice_124
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (2976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_125 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3000 3024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_125 :
    generatedNinthLowerSpinSourceQReplayWord 1 125 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 13)
    3000 24 0 (prefix_sizes 13) slice_125
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_126 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3024 3048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_126 :
    generatedNinthLowerSpinSourceQReplayWord 1 126 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 14)
    3024 24 0 (prefix_sizes 14) slice_126
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_127 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3048 3072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_127 :
    generatedNinthLowerSpinSourceQReplayWord 1 127 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 15)
    3048 24 0 (prefix_sizes 15) slice_127
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_07_128 :
    generatedNinthLowerSpinSourceQReplayWord 1 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part07 16)
    3072 24 0 (prefix_sizes 16) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords01.extract 112 128 =
      generatedNinthLowerSpinLiteralQReplayLetters01Part07 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_01_part_07 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 1 ⟨112 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters01Part07.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords01
    generatedNinthLowerSpinLiteralQReplayLetters01Part07
    112 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords01.getD (112 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
