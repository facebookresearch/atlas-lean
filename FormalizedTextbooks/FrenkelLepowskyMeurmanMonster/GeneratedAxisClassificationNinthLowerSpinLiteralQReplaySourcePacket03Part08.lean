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
def generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 : Fin 17 → Array ℕ :=
  ![
    #[28011211, 27887324, 8038515, 25779072, 20310449, 26076763, 4635715, 25717430,
      682035, 19319328, 7479534, 20695040, 16916544, 4804143, 19460121, 3382831,
      19482223, 22147396, 21159723, 1229060, 4309081, 20604992, 4945707, 14736656],
    #[9702709, 28996721, 22432032, 28723326, 20589135, 11698597, 23879024, 8654821,
      420096, 1427597, 23843600, 19789824, 18087968, 24137169, 2967220, 20733393,
      2131441, 23954455, 21064166, 1598519, 23369364, 18634784, 4768230, 14421027],
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
      792308, 22027807, 2253035, 23998229, 24570401, 25090314, 18004203, 13963906],
    #[8853340, 11884295, 21188312, 11381912, 20795504, 8561182, 1188848, 14090737,
      3345874, 2787488, 2941717, 19965952, 6214410, 16813056, 6546218, 19954688,
      8353546, 17245280, 4803434, 5875562, 17653792, 7781130, 23696234, 25695439],
    #[11072706, 27709866, 4651125, 10213528, 18575472, 25735981, 17502222, 15602287,
      19328895, 2918592, 19965510, 19965952, 24033034, 18922496, 24491850, 16804864,
      21959434, 17245280, 23662442, 24765290, 17522752, 24563466, 5896042, 9627132],
    #[14229119, 26937952, 25093152, 25643123, 16927441, 29404884, 4259854, 10595862,
      17908436, 4457103, 24827448, 22706176, 21145332, 23404542, 202036, 22401022,
      6922506, 22027807, 3430165, 24647915, 19137472, 19140340, 24579861, 32524140],
    #[30416353, 10361005, 23991360, 10316064, 18000593, 30664825, 22995952, 26077989,
      18015353, 24838417, 5206165, 24942592, 23588921, 4456446, 20557927, 7548926,
      21686215, 5840257, 18350662, 24292792, 19726430, 18982969, 5089862, 14644370],
    #[8421537, 8886163, 20448318, 16335405, 21956166, 29857568, 3472278, 9391320,
      24549598, 21912769, 1428622, 18696192, 3157216, 17728614, 18787358, 17753190,
      4866182, 7059776, 1888710, 21411232, 381182, 2954464, 16808390, 8736399],
    #[31853715, 25844090, 19222241, 26029784, 23705144, 12236247, 3997813, 15080525,
      17080753, 24705676, 1087167, 19105792, 8167248, 19448861, 2256064, 25019421,
      2032461, 5966796, 20070529, 22090908, 17372048, 329552, 2947201, 11960646],
    #[13434304, 12578743, 3522177, 27814005, 8007829, 10105303, 17725144, 30662272,
      746063, 6015041, 615745, 19240960, 6651086, 17692336, 2387104, 25040560,
      1380990, 23205970, 18985516, 5313692, 20316270, 787662, 4131372, 8779755],
    #[15603069, 27595351, 21631304, 15713312, 3837070, 29711436, 1334345, 31780533,
      19158071, 7427133, 6814671, 19916800, 3532159, 3755940, 2956432, 7872420,
      22078171, 24370174, 7504165, 2657921, 23235055, 7155071, 23079205, 27621799],
    #[32375262, 31890699, 3082688, 15674847, 26303, 15675198, 21064143, 27550037,
      22539024, 21926418, 2069876, 24836096, 2310864, 7613844, 2352513, 6495636,
      8058692, 24970136, 22826204, 20152648, 2807633, 7334608, 390364, 29621917],
    #[27339197, 28444941, 3142275, 31664574, 22708311, 32276201, 3329392, 26076685,
      7791416, 23173178, 5878831, 16992256, 16953787, 3304577, 6877504, 4521089,
      1258810, 21768315, 17540417, 3885504, 20943099, 23308731, 6036801, 14193016]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters03Part08 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters03Part08.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_128 :
    generatedNinthLowerSpinSourceQReplayWord 3 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 0)
    3072 24 0 (prefix_sizes 0) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_129 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3096 3120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_129 :
    generatedNinthLowerSpinSourceQReplayWord 3 129 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 1)
    3096 24 0 (prefix_sizes 1) slice_129
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_130 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3120 3144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_130 :
    generatedNinthLowerSpinSourceQReplayWord 3 130 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 2)
    3120 24 0 (prefix_sizes 2) slice_130
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_131 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3144 3168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_131 :
    generatedNinthLowerSpinSourceQReplayWord 3 131 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 3)
    3144 24 0 (prefix_sizes 3) slice_131
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_132 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3168 3192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_132 :
    generatedNinthLowerSpinSourceQReplayWord 3 132 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 4)
    3168 24 0 (prefix_sizes 4) slice_132
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_133 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3192 3216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_133 :
    generatedNinthLowerSpinSourceQReplayWord 3 133 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 5)
    3192 24 0 (prefix_sizes 5) slice_133
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_134 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3216 3240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_134 :
    generatedNinthLowerSpinSourceQReplayWord 3 134 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 6)
    3216 24 0 (prefix_sizes 6) slice_134
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_135 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3240 3264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_135 :
    generatedNinthLowerSpinSourceQReplayWord 3 135 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 7)
    3240 24 0 (prefix_sizes 7) slice_135
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_136 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3264 3288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_136 :
    generatedNinthLowerSpinSourceQReplayWord 3 136 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 8)
    3264 24 0 (prefix_sizes 8) slice_136
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_137 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3288 3312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_137 :
    generatedNinthLowerSpinSourceQReplayWord 3 137 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 9)
    3288 24 0 (prefix_sizes 9) slice_137
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_138 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3312 3336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_138 :
    generatedNinthLowerSpinSourceQReplayWord 3 138 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 10)
    3312 24 0 (prefix_sizes 10) slice_138
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_139 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3336 3360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_139 :
    generatedNinthLowerSpinSourceQReplayWord 3 139 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 11)
    3336 24 0 (prefix_sizes 11) slice_139
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_140 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3360 3384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_140 :
    generatedNinthLowerSpinSourceQReplayWord 3 140 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 12)
    3360 24 0 (prefix_sizes 12) slice_140
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_141 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3384 3408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_141 :
    generatedNinthLowerSpinSourceQReplayWord 3 141 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 13)
    3384 24 0 (prefix_sizes 13) slice_141
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_142 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3408 3432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_142 :
    generatedNinthLowerSpinSourceQReplayWord 3 142 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 14)
    3408 24 0 (prefix_sizes 14) slice_142
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_143 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3432 3456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_143 :
    generatedNinthLowerSpinSourceQReplayWord 3 143 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 15)
    3432 24 0 (prefix_sizes 15) slice_143
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_08_144 :
    generatedNinthLowerSpinSourceQReplayWord 3 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part08 16)
    3456 24 0 (prefix_sizes 16) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords03.extract 128 144 =
      generatedNinthLowerSpinLiteralQReplayLetters03Part08 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_03_part_08 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 3 ⟨128 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters03Part08.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords03
    generatedNinthLowerSpinLiteralQReplayLetters03Part08
    128 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords03.getD (128 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
