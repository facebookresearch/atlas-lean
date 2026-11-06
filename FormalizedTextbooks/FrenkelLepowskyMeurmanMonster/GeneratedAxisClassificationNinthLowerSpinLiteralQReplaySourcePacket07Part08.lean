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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 : Fin 17 → Array ℕ :=
  ![
    #[26263848, 26537868, 3967439, 16535822, 17074965, 16001199, 22542040, 10636600,
      21746188, 5817735, 22839436, 3964928, 20149187, 25095064, 8321864, 8184728,
      18694235, 5584394, 2344529, 22595017, 4161675, 18414531, 18071121, 30882722],
    #[11318395, 11349106, 19687887, 14267331, 2678342, 13121948, 6570101, 28842091,
      22995137, 25068007, 8036492, 2797568, 24846, 7429222, 6388950, 23422054,
      71016, 23024441, 3352145, 23179831, 20313560, 903438, 20139601, 32971714],
    #[10637258, 14897605, 5958729, 12229697, 7406289, 12665078, 4483990, 9891747,
      814403, 17408878, 24694217, 5926912, 20408586, 19478526, 2337579, 6975486,
      18654964, 19375647, 21324011, 651029, 4037153, 24027402, 7715051, 9361742],
    #[10901020, 11066951, 18855640, 15916504, 2840688, 10742622, 21418992, 27439281,
      1590738, 18153632, 22762261, 3186688, 2714378, 18908160, 19436330, 1080320,
      19449610, 18426976, 16841578, 19928938, 3252256, 66314, 2106218, 29601167],
    #[25535697, 8473017, 2932853, 29915275, 2967664, 27650878, 4788238, 8471164,
      19629951, 16982208, 5764678, 3186688, 17428234, 18908160, 1582922, 23552,
      2650890, 18426976, 1077098, 45930, 106560, 17929994, 18913130, 31690223],
    #[25825724, 33033635, 24255520, 27199408, 3478225, 26454295, 17633294, 29274581,
      21056212, 19450511, 2500152, 5926912, 18767604, 19478526, 24110388, 1699838,
      24736010, 19375647, 22230805, 5462251, 1311680, 24704756, 1077013, 13942959],
    #[9498863, 31387043, 21285952, 9442350, 2486993, 9637239, 2372592, 28825131,
      22154361, 3221777, 19218581, 8163328, 17680441, 1648638, 5476455, 19529726,
      7997383, 4081025, 5222982, 8375736, 2953310, 21729337, 18487878, 14205340],
    #[27423082, 10607033, 200919, 13154427, 530544, 26603470, 21188700, 26515068,
      3770052, 2334768, 4237309, 1060864, 3276307, 2118656, 358051, 16813056,
      3486227, 3779728, 2670211, 20492931, 303280, 787987, 20448899, 15599862],
    #[13226920, 14085086, 23014006, 13181848, 21742745, 11045916, 1765822, 16457923,
      18896662, 23027740, 7530497, 999424, 636256, 1410130, 18370997, 24652882,
      4553010, 4181152, 3749266, 22321600, 22219989, 2645344, 24022418, 9872222],
    #[29346786, 30377077, 20784799, 14154750, 22295215, 32805225, 18888159, 31857741,
      6964075, 1211707, 4838671, 7532544, 20102644, 1590754, 721630, 21376482,
      5922838, 17439932, 4889770, 1323336, 22189866, 22820340, 18031786, 32678076],
    #[28257250, 16392920, 20116737, 29826046, 8061265, 30140151, 447967, 13885056,
      23717318, 1182011, 5231983, 7610368, 18360519, 19633967, 66445, 4534063,
      6543336, 1899740, 22268724, 1983515, 6615882, 23478471, 2786100, 16031964],
    #[8737704, 8719287, 16820239, 25535384, 7429889, 11385243, 19726782, 15003317,
      575359, 17151970, 2097632, 7622656, 21583728, 21912100, 23559610, 2331172,
      19768660, 2204993, 20246549, 24207921, 6574794, 19152752, 1091605, 12864191],
    #[25186666, 15111593, 19589107, 32151675, 19335179, 31003788, 655452, 10772821,
      1424084, 18066518, 987298, 3031040, 8217895, 18391849, 8324782, 7174953,
      16780814, 5520335, 1795521, 7524072, 1600393, 6470951, 21663169, 10600361],
    #[13631727, 11665773, 7581851, 30467118, 19263231, 27549105, 20906992, 9299469,
      23404727, 4695308, 594016, 5369856, 18262060, 19863512, 597146, 6909912,
      20998132, 5432692, 4371072, 5492056, 2100406, 17825836, 16788096, 16028009],
    #[32117180, 28127987, 25105864, 16713648, 2768225, 28024399, 4110, 9303661,
      7959940, 22774847, 3735648, 7405568, 2517068, 17850438, 3586916, 6735942,
      8323082, 22577223, 21454925, 7948299, 18840360, 2146380, 206925, 30140151],
    #[25298129, 31655257, 18310682, 13621387, 510203, 32752862, 16777230, 11432439,
      490399, 18577743, 1032354, 770048, 22521221, 173963, 21959342, 22523787,
      17832462, 4635268, 3743882, 22011649, 159531, 21527941, 21878922, 12303115],
    #[11654684, 16536231, 3924777, 31808984, 2985384, 32122688, 984048, 26793367,
      1218866, 3901775, 3146556, 3006464, 5124635, 3264806, 4441085, 21117222,
      3943229, 6683721, 3577716, 24497746, 16849382, 7461403, 24424308, 11074982]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part08 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (13, false), (12, true), (12, true),
  (12, true), (13, false), (12, false), (12, false),
  (12, false), (13, true), (12, true), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part08.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_128 :
    generatedNinthLowerSpinSourceQReplayWord 7 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 0)
    3072 24 0 (prefix_sizes 0) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_129 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3096 3120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_129 :
    generatedNinthLowerSpinSourceQReplayWord 7 129 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 1)
    3096 24 0 (prefix_sizes 1) slice_129
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_130 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3120 3144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_130 :
    generatedNinthLowerSpinSourceQReplayWord 7 130 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 2)
    3120 24 0 (prefix_sizes 2) slice_130
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_131 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3144 3168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_131 :
    generatedNinthLowerSpinSourceQReplayWord 7 131 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 3)
    3144 24 0 (prefix_sizes 3) slice_131
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_132 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3168 3192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_132 :
    generatedNinthLowerSpinSourceQReplayWord 7 132 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 4)
    3168 24 0 (prefix_sizes 4) slice_132
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_133 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3192 3216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_133 :
    generatedNinthLowerSpinSourceQReplayWord 7 133 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 5)
    3192 24 0 (prefix_sizes 5) slice_133
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_134 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3216 3240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_134 :
    generatedNinthLowerSpinSourceQReplayWord 7 134 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 6)
    3216 24 0 (prefix_sizes 6) slice_134
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_135 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3240 3264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_135 :
    generatedNinthLowerSpinSourceQReplayWord 7 135 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 7)
    3240 24 0 (prefix_sizes 7) slice_135
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_136 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3264 3288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_136 :
    generatedNinthLowerSpinSourceQReplayWord 7 136 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 8)
    3264 24 0 (prefix_sizes 8) slice_136
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_137 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3288 3312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_137 :
    generatedNinthLowerSpinSourceQReplayWord 7 137 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 9)
    3288 24 0 (prefix_sizes 9) slice_137
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_138 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3312 3336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_138 :
    generatedNinthLowerSpinSourceQReplayWord 7 138 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 10)
    3312 24 0 (prefix_sizes 10) slice_138
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_139 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3336 3360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_139 :
    generatedNinthLowerSpinSourceQReplayWord 7 139 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 11)
    3336 24 0 (prefix_sizes 11) slice_139
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_140 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3360 3384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_140 :
    generatedNinthLowerSpinSourceQReplayWord 7 140 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 12)
    3360 24 0 (prefix_sizes 12) slice_140
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_141 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3384 3408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_141 :
    generatedNinthLowerSpinSourceQReplayWord 7 141 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 13)
    3384 24 0 (prefix_sizes 13) slice_141
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_142 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3408 3432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_142 :
    generatedNinthLowerSpinSourceQReplayWord 7 142 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 14)
    3408 24 0 (prefix_sizes 14) slice_142
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_143 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3432 3456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_143 :
    generatedNinthLowerSpinSourceQReplayWord 7 143 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 15)
    3432 24 0 (prefix_sizes 15) slice_143
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_08_144 :
    generatedNinthLowerSpinSourceQReplayWord 7 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part08 16)
    3456 24 0 (prefix_sizes 16) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 128 144 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part08 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_08 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨128 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part08.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part08
    128 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (128 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
