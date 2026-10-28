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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 : Fin 17 → Array ℕ :=
  ![
    #[29092386, 31034632, 4331848, 9096063, 7767182, 11797267, 1334345, 12593642,
      22770743, 2806845, 4539343, 19916800, 4375935, 7133092, 1025168, 2983844,
      24271579, 20960254, 1847589, 1287809, 20386287, 1707391, 954661, 31454968],
    #[11312161, 11398742, 24225409, 10549652, 3287189, 14753846, 17725144, 33179489,
      234063, 4737089, 1510721, 19240960, 2727118, 23035568, 3802272, 19701424,
      752254, 19529810, 24625708, 5631132, 23365742, 4252878, 23687724, 9627146],
    #[12549868, 28818181, 7841505, 27024551, 20008504, 13547432, 3997813, 15103538,
      17584561, 22903436, 4124351, 19105792, 2527056, 22850589, 791744, 17411101,
      3242829, 259020, 21282945, 22281372, 25000848, 6231888, 22704257, 25715513],
    #[26388529, 26013443, 1989694, 15690429, 23350854, 14802864, 3472278, 27204680,
      22067422, 22813889, 2335886, 18696192, 3169504, 20487270, 19448862, 20511846,
      8136838, 4256064, 127430, 23956896, 3393790, 2974944, 1921478, 25966111],
    #[9852179, 31637599, 5524544, 9908690, 23851729, 14917771, 22995952, 11697111,
      17986681, 17666321, 8022165, 24942592, 22884409, 4990974, 17606759, 8189950,
      25165767, 2114945, 22299206, 20002232, 19060830, 18573369, 16900678, 31505504],
    #[25195891, 32424300, 5409824, 27587455, 23851729, 32441816, 4259854, 11652378,
      16904916, 2257551, 24759864, 22706176, 25065204, 22730750, 3380, 23726078,
      6994186, 20555295, 6223637, 19755243, 18598848, 18407156, 1943317, 32529504],
    #[29003214, 32229542, 20549749, 32399764, 16980080, 16718369, 17502222, 28930915,
      24207231, 2025664, 20495942, 19965952, 21391114, 16806912, 25014090, 18916352,
      21433098, 18828384, 24739690, 21584746, 19638336, 22945546, 21598058, 28458224],
    #[27246435, 13791032, 3991256, 13763751, 19216496, 14236193, 1188848, 9200078,
      5533138, 972960, 3463957, 19965952, 4592394, 16806912, 8117034, 19956736,
      6770442, 18828384, 4791146, 5836650, 17668128, 7240458, 6933354, 28585200],
    #[29737700, 9495787, 16845897, 15499631, 23266001, 31978968, 16837526, 8911501,
      4474179, 4655982, 1582537, 22706176, 19177738, 22730750, 17314603, 18450430,
      8163060, 20555295, 3883243, 17049365, 17154593, 24996106, 757995, 28593248],
    #[15114662, 30646703, 6420943, 12908062, 18574918, 29365313, 21651573, 14697910,
      22988993, 1874407, 21579916, 19576832, 5101838, 3148902, 17405142, 2374758,
      17694056, 19456825, 21526097, 6011447, 1093080, 4223246, 21501521, 29931039],
    #[32843531, 12812719, 24627663, 32380717, 80661, 31798924, 5891800, 15975195,
      22796812, 20712839, 4802700, 20744192, 23608259, 20937624, 17232712, 20806552,
      497755, 3302922, 22955601, 6610377, 18663563, 21214147, 24000081, 12694913],
    #[31791369, 32230545, 2342256, 11450666, 6120905, 30647733, 21486665, 15592903,
      7406340, 8233794, 3330639, 22890496, 18257524, 22683771, 1610180, 22618235,
      200207, 21616376, 19796215, 16842892, 24274864, 24211060, 21262583, 8573248],
    #[32108029, 32033404, 79139, 13957935, 18442380, 13128029, 5634511, 12574850,
      1167620, 23005382, 20722743, 23894016, 5557287, 20601902, 6054799, 24665134,
      4364297, 1943144, 23586401, 23591503, 23515048, 6435879, 24262241, 11731916],
    #[25284753, 9787861, 5972256, 31270362, 17711695, 26598401, 23879024, 13859393,
      3057920, 1017997, 20863760, 19789824, 20029472, 16803281, 7917236, 21788113,
      7671281, 22670359, 18909670, 633911, 18136724, 20576288, 19474918, 9707911],
    #[9712188, 9047595, 22143091, 15221623, 19374513, 25570988, 4635715, 13859393,
      2271283, 20617760, 2193646, 20695040, 16883776, 1676847, 24881177, 6506031,
      24780399, 21215556, 17026859, 198916, 1120345, 20572224, 17461035, 27563495],
    #[31592981, 16345892, 18126370, 26445606, 3141551, 32999316, 19800269, 31927353,
      52706, 8325669, 18143392, 21067776, 18088896, 25029160, 8085185, 20814376,
      6685160, 3670720, 3439400, 2949376, 6397185, 20859840, 1276712, 12649123],
    #[29525621, 31861946, 1988465, 8770374, 2768226, 33091690, 721408, 15887092,
      19087151, 23694885, 19056832, 22124544, 19730526, 23624837, 8085185, 19451013,
      5940443, 19607661, 17636534, 1507379, 21540511, 20011102, 19537078, 15262045]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part02 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (12, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part02.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_032 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 768 792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_032 :
    generatedNinthLowerSpinSourceQReplayWord 6 32 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 0)
    768 24 0 (prefix_sizes 0) slice_032
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_033 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 792 816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_033 :
    generatedNinthLowerSpinSourceQReplayWord 6 33 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 1)
    792 24 0 (prefix_sizes 1) slice_033
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_034 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 816 840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_034 :
    generatedNinthLowerSpinSourceQReplayWord 6 34 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 2)
    816 24 0 (prefix_sizes 2) slice_034
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_035 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 840 864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_035 :
    generatedNinthLowerSpinSourceQReplayWord 6 35 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 3)
    840 24 0 (prefix_sizes 3) slice_035
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_036 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 864 888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_036 :
    generatedNinthLowerSpinSourceQReplayWord 6 36 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 4)
    864 24 0 (prefix_sizes 4) slice_036
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_037 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 888 912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_037 :
    generatedNinthLowerSpinSourceQReplayWord 6 37 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 5)
    888 24 0 (prefix_sizes 5) slice_037
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_038 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 912 936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_038 :
    generatedNinthLowerSpinSourceQReplayWord 6 38 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 6)
    912 24 0 (prefix_sizes 6) slice_038
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_039 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 936 960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_039 :
    generatedNinthLowerSpinSourceQReplayWord 6 39 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 7)
    936 24 0 (prefix_sizes 7) slice_039
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_040 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 960 984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_040 :
    generatedNinthLowerSpinSourceQReplayWord 6 40 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 8)
    960 24 0 (prefix_sizes 8) slice_040
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_041 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 984 1008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_041 :
    generatedNinthLowerSpinSourceQReplayWord 6 41 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 9)
    984 24 0 (prefix_sizes 9) slice_041
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_042 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1008 1032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_042 :
    generatedNinthLowerSpinSourceQReplayWord 6 42 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 10)
    1008 24 0 (prefix_sizes 10) slice_042
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_043 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1032 1056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_043 :
    generatedNinthLowerSpinSourceQReplayWord 6 43 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 11)
    1032 24 0 (prefix_sizes 11) slice_043
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_044 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1056 1080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_044 :
    generatedNinthLowerSpinSourceQReplayWord 6 44 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 12)
    1056 24 0 (prefix_sizes 12) slice_044
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_045 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1080 1104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_045 :
    generatedNinthLowerSpinSourceQReplayWord 6 45 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 13)
    1080 24 0 (prefix_sizes 13) slice_045
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_046 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1104 1128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_046 :
    generatedNinthLowerSpinSourceQReplayWord 6 46 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 14)
    1104 24 0 (prefix_sizes 14) slice_046
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_047 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1128 1152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_047 :
    generatedNinthLowerSpinSourceQReplayWord 6 47 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 15)
    1128 24 0 (prefix_sizes 15) slice_047
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_048 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1152 1176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_02_048 :
    generatedNinthLowerSpinSourceQReplayWord 6 48 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part02 16)
    1152 24 0 (prefix_sizes 16) slice_048
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 32 48 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part02 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_02 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨32 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part02.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part02
    32 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (32 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
