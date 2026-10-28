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
def generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 : Fin 17 → Array ℕ :=
  ![
    #[13921039, 14937055, 20322589, 27433567, 3730788, 31773637, 17353795, 29472545,
      19737766, 6567844, 5481756, 19228672, 21384635, 5754412, 22294547, 3259948,
      289687, 18236712, 7364287, 1251475, 5332392, 19371451, 18298559, 10011911],
    #[14544891, 14177860, 3889089, 10120967, 20344607, 30319734, 8134861, 15890986,
      19527314, 5543316, 22587330, 22857728, 3283283, 1851099, 3436483, 4390619,
      7057288, 1353695, 23709783, 19185292, 21517968, 840019, 7934039, 10699277],
    #[13527382, 32186601, 3643122, 9038250, 19107250, 32572296, 23056896, 16256889,
      2439073, 21942439, 22591394, 21641216, 1190227, 17000741, 1531150, 22898981,
      21117046, 3626258, 4431204, 3230785, 4953181, 840019, 24343908, 10703469],
    #[29217534, 15537503, 22818666, 13754976, 22346914, 8977227, 17369092, 28694742,
      7713637, 18298513, 22417302, 17577984, 16819215, 1971420, 19107836, 2536668,
      7932115, 2901964, 22880031, 1602499, 22481907, 17054735, 1136415, 30252312],
    #[13241236, 12253425, 5117717, 27529701, 21254046, 9479479, 19054860, 33528765,
      6674200, 6285944, 145291, 17311744, 19539981, 6200641, 2840424, 585025,
      22314316, 17544825, 4909877, 8375924, 24457061, 21233677, 22528821, 11740878],
    #[33129339, 25388131, 22514231, 14214739, 7896455, 14920476, 787212, 31394987,
      5682890, 20709593, 20332614, 21968896, 3933437, 6386639, 5340187, 1033167,
      6471474, 22196442, 4886504, 21967911, 4405478, 7859453, 20711400, 15140219],
    #[32322598, 29430508, 1764586, 25220089, 18916162, 9924664, 3439368, 31033967,
      22539383, 25017422, 17668546, 17119232, 3430557, 8236404, 24402481, 1076596,
      21007849, 6328509, 24726868, 3946528, 17953452, 4812957, 6559060, 15977436],
    #[13931448, 12718113, 17001236, 12220074, 18903842, 10945624, 19741942, 14719473,
      7178532, 4485072, 17324911, 18024448, 17259056, 24627271, 24402481, 19712071,
      21625463, 4551280, 23398407, 665664, 16908289, 21803568, 7233543, 32172098],
    #[29792217, 25440552, 23531063, 14723002, 5401893, 32735212, 1869580, 14290011,
      5175075, 1638441, 1971631, 21985280, 3248404, 7598724, 5340187, 3703428,
      25000848, 7697809, 22175233, 21030021, 23801103, 6273300, 2397697, 31950219],
    #[29367846, 14437923, 20771655, 13152901, 3079806, 30871861, 18322782, 15899629,
      21939320, 18176552, 17375417, 24172544, 4951871, 7512001, 2840424, 5136321,
      3393790, 7884971, 20125781, 25153428, 17221719, 5183295, 5685333, 32233118],
    #[31234933, 12824029, 4146570, 16652005, 2293581, 31373003, 17082355, 32402110,
      21917816, 3205, 20747892, 24123392, 4754930, 5148402, 16908438, 4476658,
      707328, 21161368, 32408, 7387242, 814436, 8001010, 21186200, 31524781],
    #[8434586, 13800750, 16796561, 15832638, 21724372, 10693143, 24442895, 13897171,
      21944217, 5765012, 19434435, 21022720, 6001672, 6181892, 20175868, 7951364,
      19777548, 3966628, 23572136, 16831148, 5210100, 4238344, 6784680, 12863679],
    #[28317594, 15157123, 1747650, 13457261, 21825716, 29142409, 4782428, 12905939,
      22315722, 24686698, 895246, 20973568, 8192008, 5111812, 20580354, 6881284,
      1771532, 18415625, 6555653, 16973825, 20973578, 7342088, 24379397, 14182796],
    #[3192734, 6782859, 5927626, 5078885, 899248, 8140170, 17316191, 17096145,
      5515975, 7870564, 21868810, 2048, 24999936, 21936128, 24825856, 23705600,
      6012928, 18452480, 19159040, 17031168, 43008, 19953664, 7624704, 26783110],
    #[20723079, 23504966, 2894729, 23488742, 7276638, 17721279, 16779023, 19798448,
      16973684, 17455341, 4200718, 2048, 18905088, 23922688, 21000192, 23578624,
      958464, 22777856, 22145024, 20852736, 6948864, 23750656, 3033088, 27282623],
    #[3969511, 5840856, 48858, 6938392, 7404480, 20686194, 17155490, 20064483,
      19622026, 608832, 7588803, 2048, 16795648, 22792192, 21016576, 23529472,
      3051520, 24997888, 21039104, 20852736, 8189952, 21792768, 4089856, 29015436],
    #[45934, 6126377, 23229219, 8239973, 2631744, 22978753, 2124982, 399466,
      23363271, 7691661, 6960193, 2048, 24705024, 23820288, 22728704, 21608448,
      6176768, 20512768, 16844800, 17031168, 2156544, 17885184, 7407616, 11888799]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters01Part09 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (12, false), (13, true), (12, true),
  (12, true), (13, true), (12, true), (13, true),
  (14, false), (12, false), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters01Part09.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_144 :
    generatedNinthLowerSpinSourceQReplayWord 1 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 0)
    3456 24 0 (prefix_sizes 0) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_145 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3480 3504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_145 :
    generatedNinthLowerSpinSourceQReplayWord 1 145 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 1)
    3480 24 0 (prefix_sizes 1) slice_145
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_146 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3504 3528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_146 :
    generatedNinthLowerSpinSourceQReplayWord 1 146 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 2)
    3504 24 0 (prefix_sizes 2) slice_146
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_147 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3528 3552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_147 :
    generatedNinthLowerSpinSourceQReplayWord 1 147 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 3)
    3528 24 0 (prefix_sizes 3) slice_147
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_148 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3552 3576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_148 :
    generatedNinthLowerSpinSourceQReplayWord 1 148 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 4)
    3552 24 0 (prefix_sizes 4) slice_148
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_149 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3576 3600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_149 :
    generatedNinthLowerSpinSourceQReplayWord 1 149 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 5)
    3576 24 0 (prefix_sizes 5) slice_149
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_150 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3600 3624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_150 :
    generatedNinthLowerSpinSourceQReplayWord 1 150 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 6)
    3600 24 0 (prefix_sizes 6) slice_150
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_151 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3624 3648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_151 :
    generatedNinthLowerSpinSourceQReplayWord 1 151 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 7)
    3624 24 0 (prefix_sizes 7) slice_151
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_152 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3648 3672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_152 :
    generatedNinthLowerSpinSourceQReplayWord 1 152 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 8)
    3648 24 0 (prefix_sizes 8) slice_152
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_153 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3672 3696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_153 :
    generatedNinthLowerSpinSourceQReplayWord 1 153 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 9)
    3672 24 0 (prefix_sizes 9) slice_153
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_154 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3696 3720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_154 :
    generatedNinthLowerSpinSourceQReplayWord 1 154 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 10)
    3696 24 0 (prefix_sizes 10) slice_154
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_155 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3720 3744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_155 :
    generatedNinthLowerSpinSourceQReplayWord 1 155 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 11)
    3720 24 0 (prefix_sizes 11) slice_155
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_156 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3744 3768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_156 :
    generatedNinthLowerSpinSourceQReplayWord 1 156 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 12)
    3744 24 0 (prefix_sizes 12) slice_156
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_157 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3768 3792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_157 :
    generatedNinthLowerSpinSourceQReplayWord 1 157 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 13)
    3768 24 0 (prefix_sizes 13) slice_157
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_158 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3792 3816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_158 :
    generatedNinthLowerSpinSourceQReplayWord 1 158 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 14)
    3792 24 0 (prefix_sizes 14) slice_158
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_159 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3816 3840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_159 :
    generatedNinthLowerSpinSourceQReplayWord 1 159 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 15)
    3816 24 0 (prefix_sizes 15) slice_159
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_09_160 :
    generatedNinthLowerSpinSourceQReplayWord 1 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part09 16)
    3840 24 0 (prefix_sizes 16) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords01.extract 144 160 =
      generatedNinthLowerSpinLiteralQReplayLetters01Part09 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_01_part_09 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 1 ⟨144 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters01Part09.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords01
    generatedNinthLowerSpinLiteralQReplayLetters01Part09
    144 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords01.getD (144 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
