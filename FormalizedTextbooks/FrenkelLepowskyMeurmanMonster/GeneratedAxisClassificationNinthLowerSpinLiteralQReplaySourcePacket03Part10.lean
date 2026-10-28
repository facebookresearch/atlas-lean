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
def generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 : Fin 15 → Array ℕ :=
  ![
    #[20375430, 6650183, 21564229, 5929591, 3356720, 25023251, 17155490, 3694210,
      22093077, 4533295, 24366019, 2048, 21776384, 23529472, 4239360, 22792192,
      6180864, 3432448, 17242112, 3874816, 19986432, 16812032, 7895040, 12245997],
    #[3339161, 7011200, 3339142, 7011216, 21035036, 19198006, 2124982, 3430557,
      18628194, 527732, 23737409, 2048, 19982336, 21608448, 5951488, 23820288,
      3444736, 7733248, 21235712, 323584, 23656448, 22607872, 3409920, 9058408],
    #[24364785, 7181509, 5515211, 23615742, 517435, 1268498, 2669449, 3933437,
      17491190, 3568591, 21345752, 2048, 23259136, 23058432, 2125824, 24868864,
      1323008, 4575232, 17565696, 3022848, 18974720, 19613696, 4642816, 26555298],
    #[23547909, 4481809, 22131475, 3885150, 24754763, 18384185, 4489930, 19539981,
      4144908, 1961281, 1030689, 2048, 19699712, 19757056, 8220672, 20318208,
      4411392, 6750208, 17303552, 4489216, 22960128, 24729600, 6621184, 8536556],
    #[24299176, 7889474, 24396222, 3296192, 23084469, 16843463, 5175193, 19479200,
      2153714, 1191615, 2710049, 2048, 18520064, 18577408, 6000640, 20318208,
      5611520, 6799360, 19412992, 4345856, 21936128, 23705600, 7600128, 26783967],
    #[7128728, 6932682, 3051612, 5032583, 2349405, 3630964, 868472, 24200042,
      3153774, 25102423, 24266200, 2048, 18454528, 19179520, 1540096, 24868864,
      1875968, 8048640, 21030912, 5582848, 23922688, 23578624, 5130240, 11560524],
    #[7946325, 7769940, 20865084, 22252825, 846499, 573578, 2823288, 4269930,
      16781166, 7695716, 5816459, 2048, 19499008, 17999872, 499712, 23955456,
      3833856, 4984832, 22022144, 5496832, 22792192, 23529472, 8296448, 27497697],
    #[747009, 20065802, 17537553, 3451187, 20479897, 21635149, 20461347, 24882965,
      5852697, 22368031, 7700400, 2048, 23394304, 22657024, 6291456, 23324672,
      1458176, 262144, 25143296, 4296704, 17737728, 21354496, 1984512, 9705645],
    #[18585185, 564025, 1796721, 1349939, 18021066, 24769152, 19727854, 7801414,
      8325753, 7761330, 7117870, 2048, 21108736, 24725504, 4255744, 22358016,
      1458176, 2236416, 25126912, 4280320, 19830784, 21170176, 4093952, 27724384],
    #[22413559, 4513311, 1122462, 22416665, 20052810, 19875265, 19661107, 8169091,
      1088414, 8235149, 7880827, 2048, 17373184, 20391936, 2236416, 21514240,
      3833856, 5013504, 24119296, 7593984, 22956032, 21108736, 8067072, 27529642],
    #[22713937, 2507872, 21909756, 7880546, 8138375, 3801109, 4863257, 7495058,
      2050288, 18802886, 723864, 2048, 17766400, 17627136, 5013504, 24967168,
      5582848, 1105920, 21682176, 2158592, 20875264, 17373184, 448512, 33293284],
    #[22713937, 2507872, 5132540, 7880546, 21190937, 18437816, 7684743, 7819103,
      3102960, 16887640, 17976422, 2048, 20908032, 19585024, 6971392, 23726080,
      5496832, 1105920, 21760000, 2158592, 20875264, 17373184, 448512, 31802394],
    #[6095083, 1086704, 5890384, 5045746, 23755568, 6830735, 6648768, 25035233,
      4151376, 17500128, 2525182, 2048, 16828416, 23767040, 3174400, 16820224,
      6766592, 2445312, 21501952, 2457600, 18425856, 17766400, 2430976, 11358823],
    #[3754858, 4146178, 23587258, 2966536, 20621328, 2162880, 3186752, 18978912,
      24651966, 23709749, 3163136, 2048, 18876416, 17856512, 3145728, 17881088,
      3227648, 3690496, 17700864, 1196032, 16799744, 16783360, 4237312, 8982443],
    #[3754858, 19547138, 21213626, 19464, 3821584, 90304, 64, 17905760,
      6885566, 22100021, 3163136, 2048, 18876416, 17856512, 3145728, 17881088,
      3227648, 3690496, 921600, 17975296, 16799744, 16783360, 4237312, 11048843]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters03Part10 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (12, true), (13, true),
  (12, false), (13, true), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (5, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 15,
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters03Part10.size = 14 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_160 :
    generatedNinthLowerSpinSourceQReplayWord 3 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 0)
    3840 24 0 (prefix_sizes 0) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_161 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3864 3888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_161 :
    generatedNinthLowerSpinSourceQReplayWord 3 161 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 1)
    3864 24 0 (prefix_sizes 1) slice_161
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_162 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3888 3912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_162 :
    generatedNinthLowerSpinSourceQReplayWord 3 162 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 2)
    3888 24 0 (prefix_sizes 2) slice_162
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_163 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3912 3936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_163 :
    generatedNinthLowerSpinSourceQReplayWord 3 163 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 3)
    3912 24 0 (prefix_sizes 3) slice_163
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_164 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3936 3960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_164 :
    generatedNinthLowerSpinSourceQReplayWord 3 164 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 4)
    3936 24 0 (prefix_sizes 4) slice_164
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_165 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3960 3984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_165 :
    generatedNinthLowerSpinSourceQReplayWord 3 165 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 5)
    3960 24 0 (prefix_sizes 5) slice_165
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_166 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3984 4008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_166 :
    generatedNinthLowerSpinSourceQReplayWord 3 166 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 6)
    3984 24 0 (prefix_sizes 6) slice_166
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_167 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4008 4032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_167 :
    generatedNinthLowerSpinSourceQReplayWord 3 167 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 7)
    4008 24 0 (prefix_sizes 7) slice_167
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_168 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4032 4056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_168 :
    generatedNinthLowerSpinSourceQReplayWord 3 168 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 8)
    4032 24 0 (prefix_sizes 8) slice_168
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_169 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4056 4080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_169 :
    generatedNinthLowerSpinSourceQReplayWord 3 169 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 9)
    4056 24 0 (prefix_sizes 9) slice_169
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_170 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4080 4104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_170 :
    generatedNinthLowerSpinSourceQReplayWord 3 170 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 10)
    4080 24 0 (prefix_sizes 10) slice_170
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_171 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4104 4128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_171 :
    generatedNinthLowerSpinSourceQReplayWord 3 171 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 11)
    4104 24 0 (prefix_sizes 11) slice_171
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_172 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4128 4152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_172 :
    generatedNinthLowerSpinSourceQReplayWord 3 172 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 12)
    4128 24 0 (prefix_sizes 12) slice_172
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_173 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4152 4176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_173 :
    generatedNinthLowerSpinSourceQReplayWord 3 173 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 13)
    4152 24 0 (prefix_sizes 13) slice_173
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_174 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 4176 4200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_10_174 :
    generatedNinthLowerSpinSourceQReplayWord 3 174 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part10 14)
    4176 24 0 (prefix_sizes 14) slice_174
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (4176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords03.extract 160 174 =
      generatedNinthLowerSpinLiteralQReplayLetters03Part10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_03_part_10 :
    (fun n : Fin 14 =>
      generatedNinthLowerSpinSourceQReplayLetter 3 ⟨160 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters03Part10.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords03
    generatedNinthLowerSpinLiteralQReplayLetters03Part10
    160 14 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords03.getD (160 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
