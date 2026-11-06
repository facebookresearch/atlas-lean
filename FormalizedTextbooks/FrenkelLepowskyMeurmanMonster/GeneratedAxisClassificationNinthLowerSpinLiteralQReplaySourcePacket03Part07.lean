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
def generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 : Fin 17 → Array ℕ :=
  ![
    #[30047238, 12589577, 1205321, 27717517, 17480401, 27884346, 16837526, 28990575,
      5543235, 1502062, 6864329, 22706176, 19337482, 19529726, 24685355, 23769086,
      792308, 22027807, 2253035, 23998229, 24570401, 25090314, 18004203, 13963906],
    #[8853340, 11884295, 21188312, 11381912, 20795504, 8561182, 1188848, 14090737,
      3345874, 2787488, 2941717, 19965952, 6214410, 16813056, 6546218, 19954688,
      8353546, 17245280, 4803434, 5875562, 17653792, 7781130, 23696234, 25695439],
    #[11072706, 27709866, 4651125, 10213528, 18575472, 25735981, 17502222, 15602287,
      19328895, 2918592, 19965510, 19965952, 24033034, 18922496, 24491850, 16804864,
      21959434, 17245280, 23662442, 24765290, 17522752, 24563466, 5896042, 9627132],
    #[8853340, 11884295, 21188312, 11381912, 20795504, 8561182, 1188848, 14090737,
      3345874, 2787488, 2941717, 19965952, 6214410, 16813056, 6546218, 19954688,
      8353546, 17245280, 4803434, 5875562, 17653792, 7781130, 23696234, 25695439],
    #[30047238, 12589577, 1205321, 27717517, 17480401, 27884346, 16837526, 28990575,
      5543235, 1502062, 6864329, 22706176, 19337482, 19529726, 24685355, 23769086,
      792308, 22027807, 2253035, 23998229, 24570401, 25090314, 18004203, 13963906],
    #[16434684, 10507765, 21381583, 28217924, 24946246, 27148315, 21651573, 29379052,
      22964417, 6162919, 17825932, 19576832, 6998286, 5133414, 22076630, 5923942,
      22328680, 21965625, 24573521, 1794615, 7271896, 6775054, 7773777, 27275845],
    #[32560335, 10039915, 5272015, 10298601, 6697749, 26490184, 5891800, 13387999,
      23816716, 24661383, 1097868, 20744192, 25115587, 24245144, 23034696, 24376216,
      6164571, 5598730, 23119441, 1365449, 22167691, 22328259, 5291601, 11957829],
    #[10056322, 16267034, 21783920, 31044257, 1621449, 15437374, 21486665, 32829004,
      2384644, 7111490, 2705999, 22890496, 19670644, 24840315, 199108, 24643707,
      1611279, 17567480, 24137975, 25061516, 22237104, 21749364, 1718519, 13564619],
    #[33432133, 26277316, 24706339, 30946455, 24076428, 13549285, 5634511, 29095738,
      3305732, 23955654, 23374903, 23894016, 961575, 20489262, 326543, 24814638,
      1703945, 7057000, 21591649, 21729871, 23345064, 3691559, 6073953, 8555636],
    #[9702709, 28996721, 22432032, 28723326, 20589135, 11698597, 23879024, 8654821,
      420096, 1427597, 23843600, 19789824, 18087968, 24137169, 2967220, 20733393,
      2131441, 23954455, 21064166, 1598519, 23369364, 18634784, 4768230, 14421027],
    #[28011211, 27887324, 8038515, 25779072, 20310449, 26076763, 4635715, 25717430,
      682035, 19319328, 7479534, 20695040, 16916544, 4804143, 19460121, 3382831,
      19482223, 22147396, 21159723, 1229060, 4309081, 20604992, 4945707, 14736656],
    #[31620212, 29205829, 5008930, 29194567, 681903, 11123189, 19800269, 32942680,
      3345890, 1219109, 19943584, 21067776, 25113536, 20075048, 6280897, 24257064,
      4360680, 1936064, 3504936, 6535424, 3024129, 22379456, 17986344, 16719042],
    #[29632628, 28496571, 22433649, 26074439, 3781986, 11595371, 721408, 32836853,
      19332911, 19070501, 18899136, 22124544, 23117918, 19334277, 7993025, 23573637,
      5770459, 20494445, 18627766, 4806707, 17290911, 24938590, 3880118, 15732572],
    #[28498909, 14433957, 275162, 11200973, 3251485, 25503972, 964612, 30825105,
      18764324, 3754794, 24918671, 18384896, 7389438, 3393600, 23607944, 1689664,
      4894910, 3177756, 6854050, 7486946, 18053750, 1198334, 23223714, 28312582],
    #[29632628, 28496571, 22433649, 26074439, 3781986, 11595371, 721408, 32836853,
      19332911, 19070501, 18899136, 22124544, 23117918, 19334277, 7993025, 23573637,
      5770459, 20494445, 18627766, 4806707, 17290911, 24938590, 3880118, 15732572],
    #[31620212, 29205829, 5008930, 29194567, 681903, 11123189, 19800269, 32942680,
      3345890, 1219109, 19943584, 21067776, 25113536, 20075048, 6280897, 24257064,
      4360680, 1936064, 3504936, 6535424, 3024129, 22379456, 17986344, 16719042],
    #[28011211, 27887324, 8038515, 25779072, 20310449, 26076763, 4635715, 25717430,
      682035, 19319328, 7479534, 20695040, 16916544, 4804143, 19460121, 3382831,
      19482223, 22147396, 21159723, 1229060, 4309081, 20604992, 4945707, 14736656]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters03Part07 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters03Part07.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_112 :
    generatedNinthLowerSpinSourceQReplayWord 3 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 0)
    2688 24 0 (prefix_sizes 0) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_113 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2712 2736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_113 :
    generatedNinthLowerSpinSourceQReplayWord 3 113 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 1)
    2712 24 0 (prefix_sizes 1) slice_113
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_114 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2736 2760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_114 :
    generatedNinthLowerSpinSourceQReplayWord 3 114 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 2)
    2736 24 0 (prefix_sizes 2) slice_114
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_115 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2760 2784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_115 :
    generatedNinthLowerSpinSourceQReplayWord 3 115 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 3)
    2760 24 0 (prefix_sizes 3) slice_115
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_116 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2784 2808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_116 :
    generatedNinthLowerSpinSourceQReplayWord 3 116 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 4)
    2784 24 0 (prefix_sizes 4) slice_116
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_117 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2808 2832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_117 :
    generatedNinthLowerSpinSourceQReplayWord 3 117 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 5)
    2808 24 0 (prefix_sizes 5) slice_117
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_118 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2832 2856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_118 :
    generatedNinthLowerSpinSourceQReplayWord 3 118 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 6)
    2832 24 0 (prefix_sizes 6) slice_118
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_119 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2856 2880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_119 :
    generatedNinthLowerSpinSourceQReplayWord 3 119 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 7)
    2856 24 0 (prefix_sizes 7) slice_119
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_120 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2880 2904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_120 :
    generatedNinthLowerSpinSourceQReplayWord 3 120 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 8)
    2880 24 0 (prefix_sizes 8) slice_120
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_121 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2904 2928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_121 :
    generatedNinthLowerSpinSourceQReplayWord 3 121 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 9)
    2904 24 0 (prefix_sizes 9) slice_121
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_122 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2928 2952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_122 :
    generatedNinthLowerSpinSourceQReplayWord 3 122 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 10)
    2928 24 0 (prefix_sizes 10) slice_122
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_123 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2952 2976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_123 :
    generatedNinthLowerSpinSourceQReplayWord 3 123 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 11)
    2952 24 0 (prefix_sizes 11) slice_123
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_124 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 2976 3000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_124 :
    generatedNinthLowerSpinSourceQReplayWord 3 124 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 12)
    2976 24 0 (prefix_sizes 12) slice_124
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (2976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_125 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3000 3024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_125 :
    generatedNinthLowerSpinSourceQReplayWord 3 125 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 13)
    3000 24 0 (prefix_sizes 13) slice_125
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_126 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3024 3048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_126 :
    generatedNinthLowerSpinSourceQReplayWord 3 126 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 14)
    3024 24 0 (prefix_sizes 14) slice_126
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_127 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3048 3072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_127 :
    generatedNinthLowerSpinSourceQReplayWord 3 127 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 15)
    3048 24 0 (prefix_sizes 15) slice_127
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_07_128 :
    generatedNinthLowerSpinSourceQReplayWord 3 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part07 16)
    3072 24 0 (prefix_sizes 16) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords03.extract 112 128 =
      generatedNinthLowerSpinLiteralQReplayLetters03Part07 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_03_part_07 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 3 ⟨112 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters03Part07.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords03
    generatedNinthLowerSpinLiteralQReplayLetters03Part07
    112 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords03.getD (112 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
