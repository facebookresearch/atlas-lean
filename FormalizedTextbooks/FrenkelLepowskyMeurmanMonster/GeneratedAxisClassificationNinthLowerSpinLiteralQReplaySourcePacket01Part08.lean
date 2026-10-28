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
def generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 : Fin 17 → Array ℕ :=
  ![
    #[14626273, 31904933, 4288800, 27678890, 24052303, 14694769, 23879024, 30355249,
      17350912, 1785997, 7066384, 19789824, 17668128, 20733393, 19744436, 24137169,
      7671281, 7642135, 17691110, 18408503, 8195732, 17154080, 285158, 29502711],
    #[15012914, 30430131, 3777827, 30032608, 19343500, 13570194, 5634511, 10535245,
      23705860, 25059526, 6597687, 23894016, 1324071, 24814638, 17103759, 20489262,
      4364297, 19514984, 22253153, 1270351, 8302504, 2280487, 4609633, 26860035],
    #[11183424, 30568664, 4164976, 26711395, 6571465, 29409788, 21486665, 13056398,
      21961476, 4971330, 19483215, 22890496, 20233844, 24643707, 16976324, 24840315,
      200207, 4183800, 22550775, 5580940, 4970416, 22234740, 3305719, 30276873],
    #[30933459, 28014455, 24152527, 30671349, 4643605, 31942740, 5891800, 31759811,
      1053196, 16975239, 17875084, 20744192, 19182531, 24376216, 6257480, 24245144,
      497755, 24622602, 18587217, 23954889, 641163, 17775555, 2877009, 12481369],
    #[30339539, 12120538, 6732239, 15447659, 23879238, 31919156, 21651573, 32800195,
      3399873, 1278439, 1048716, 19576832, 2601230, 5923942, 5299414, 5133414,
      17694056, 7070521, 17530449, 24302135, 19107288, 2758926, 726609, 10810986],
    #[29600114, 30711677, 20442185, 11463417, 19264209, 26437198, 16837526, 11766043,
      21159235, 4658030, 23641545, 22706176, 18143498, 23769086, 7908139, 19529726,
      8163060, 8107551, 7952619, 7753493, 4530721, 21827850, 21594347, 28588022],
    #[14314643, 10398920, 5310168, 10213207, 17307760, 32969169, 1188848, 25852478,
      17401298, 311456, 19718933, 19965952, 7740170, 19954688, 23323434, 16813056,
      6770442, 1465440, 4195178, 23074666, 2467872, 6189834, 23124842, 32829184],
    #[32935360, 11458728, 24285301, 11039130, 17307760, 33423919, 17502222, 28339053,
      3819391, 1237184, 3188294, 19965952, 21397258, 16804864, 7714634, 18922496,
      21433098, 1465440, 24143722, 4215658, 2336832, 22939402, 4235114, 16596222],
    #[25916797, 27775330, 5479456, 11527025, 19264209, 27332054, 4259854, 32752916,
      1047252, 6716047, 8050232, 22706176, 24211188, 22401022, 16979252, 23404542,
      6994186, 8107551, 1896213, 6322411, 1559488, 18335476, 23050005, 28925038],
    #[11826915, 10752943, 7695424, 25498146, 20255441, 11684731, 22995952, 32079911,
      810105, 24082705, 21983381, 24942592, 23214137, 7548926, 3780711, 4456446,
      25165767, 21280129, 19970630, 6999480, 2672734, 19161145, 6623814, 9858960],
    #[10630055, 29918357, 1879102, 15696171, 18931270, 13839398, 3472278, 11403230,
      6566110, 23917761, 18205838, 18696192, 402656, 17753190, 2010142, 17728614,
      8136838, 20185408, 7670214, 3081632, 20175102, 1776864, 23699910, 33041801],
    #[27229849, 30669680, 493281, 14040274, 17858104, 28884957, 3997813, 27225671,
      6101425, 17904268, 17864383, 19105792, 517968, 25019421, 19033280, 19448861,
      3242829, 21476300, 16812161, 3593372, 7498640, 8290128, 1978497, 25576268],
    #[28965625, 16390286, 18970241, 33103692, 211093, 8568558, 17725144, 10934713,
      24259151, 2285633, 17392961, 19240960, 586958, 25040560, 19164320, 17692336,
      752254, 6852690, 20273708, 20321436, 5998702, 6393038, 2875948, 25792722],
    #[31331947, 14041409, 895304, 13440822, 582798, 9877338, 1334345, 30731683,
      3127, 3133, 23591887, 19916800, 5639551, 7872420, 19733648, 3755940,
      24271579, 5628926, 7735589, 23944833, 90607, 968063, 23372069, 32643761],
    #[16699620, 14842929, 17760704, 16538853, 6692543, 9311748, 21064143, 28618863,
      394000, 23714322, 18847092, 24836096, 5417680, 6495636, 19129729, 7613844,
      1847108, 8055704, 20804828, 4555080, 22757201, 1966800, 6606044, 29622183],
    #[14121378, 32557330, 19872387, 29194657, 17057879, 14186230, 3329392, 33273362,
      20216632, 24993850, 22656047, 16992256, 21031355, 4521089, 23654720, 3304577,
      2620730, 3805307, 21585217, 17770944, 8243451, 19001787, 2024769, 28205415],
    #[13921039, 14937055, 20322589, 27433567, 3730788, 31773637, 17353795, 29472545,
      19737766, 6567844, 5481756, 19228672, 21384635, 5754412, 22294547, 3259948,
      289687, 18236712, 7364287, 1251475, 5332392, 19371451, 18298559, 10011911]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters01Part08 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (12, true), (13, true),
  (12, true), (12, true), (13, true), (12, false),
  (13, false), (12, false), (12, false), (13, false),
  (12, false), (12, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters01Part08.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_128 :
    generatedNinthLowerSpinSourceQReplayWord 1 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 0)
    3072 24 0 (prefix_sizes 0) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_129 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3096 3120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_129 :
    generatedNinthLowerSpinSourceQReplayWord 1 129 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 1)
    3096 24 0 (prefix_sizes 1) slice_129
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_130 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3120 3144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_130 :
    generatedNinthLowerSpinSourceQReplayWord 1 130 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 2)
    3120 24 0 (prefix_sizes 2) slice_130
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_131 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3144 3168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_131 :
    generatedNinthLowerSpinSourceQReplayWord 1 131 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 3)
    3144 24 0 (prefix_sizes 3) slice_131
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_132 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3168 3192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_132 :
    generatedNinthLowerSpinSourceQReplayWord 1 132 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 4)
    3168 24 0 (prefix_sizes 4) slice_132
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_133 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3192 3216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_133 :
    generatedNinthLowerSpinSourceQReplayWord 1 133 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 5)
    3192 24 0 (prefix_sizes 5) slice_133
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_134 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3216 3240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_134 :
    generatedNinthLowerSpinSourceQReplayWord 1 134 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 6)
    3216 24 0 (prefix_sizes 6) slice_134
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_135 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3240 3264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_135 :
    generatedNinthLowerSpinSourceQReplayWord 1 135 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 7)
    3240 24 0 (prefix_sizes 7) slice_135
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_136 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3264 3288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_136 :
    generatedNinthLowerSpinSourceQReplayWord 1 136 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 8)
    3264 24 0 (prefix_sizes 8) slice_136
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_137 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3288 3312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_137 :
    generatedNinthLowerSpinSourceQReplayWord 1 137 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 9)
    3288 24 0 (prefix_sizes 9) slice_137
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_138 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3312 3336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_138 :
    generatedNinthLowerSpinSourceQReplayWord 1 138 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 10)
    3312 24 0 (prefix_sizes 10) slice_138
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_139 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3336 3360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_139 :
    generatedNinthLowerSpinSourceQReplayWord 1 139 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 11)
    3336 24 0 (prefix_sizes 11) slice_139
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_140 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3360 3384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_140 :
    generatedNinthLowerSpinSourceQReplayWord 1 140 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 12)
    3360 24 0 (prefix_sizes 12) slice_140
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_141 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3384 3408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_141 :
    generatedNinthLowerSpinSourceQReplayWord 1 141 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 13)
    3384 24 0 (prefix_sizes 13) slice_141
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_142 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3408 3432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_142 :
    generatedNinthLowerSpinSourceQReplayWord 1 142 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 14)
    3408 24 0 (prefix_sizes 14) slice_142
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_143 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3432 3456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_143 :
    generatedNinthLowerSpinSourceQReplayWord 1 143 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 15)
    3432 24 0 (prefix_sizes 15) slice_143
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords01.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_01_part_08_144 :
    generatedNinthLowerSpinSourceQReplayWord 1 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords01
    (generatedNinthLowerSpinLiteralQReplayPrefixes01Part08 16)
    3456 24 0 (prefix_sizes 16) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords01.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords01.extract 128 144 =
      generatedNinthLowerSpinLiteralQReplayLetters01Part08 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_01_part_08 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 1 ⟨128 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters01Part08.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords01
    generatedNinthLowerSpinLiteralQReplayLetters01Part08
    128 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords01.getD (128 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
