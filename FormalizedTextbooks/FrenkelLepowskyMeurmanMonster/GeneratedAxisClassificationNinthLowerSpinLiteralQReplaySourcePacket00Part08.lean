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
def generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 : Fin 17 → Array ℕ :=
  ![
    #[13948783, 31609720, 22669427, 11068964, 21713329, 12639231, 4635715, 13733650,
      2271283, 5798432, 23951598, 20695040, 630848, 7585327, 20525081, 17393199,
      1586799, 7012676, 21585707, 19118340, 5998681, 20045888, 21036843, 11071668],
    #[31970754, 31188102, 7543072, 26955913, 23355983, 16107858, 23879024, 13733650,
      3057920, 21727373, 7637776, 19789824, 1675296, 23895505, 3966644, 2131409,
      20039153, 7427095, 21821926, 17378359, 24694420, 17940512, 21322214, 9979092],
    #[12852244, 31216533, 4238627, 8682182, 22145164, 14725300, 5634511, 29069675,
      1167620, 5441734, 5321783, 23894016, 18177063, 22529070, 2661263, 1428526,
      24023049, 17092200, 22185569, 4131407, 22261672, 2337831, 21452385, 11436581],
    #[13830761, 27621361, 7361904, 27372106, 103881, 31631061, 21486665, 12697255,
      7406340, 24486722, 24928847, 22890496, 4552308, 21395579, 8153540, 4550779,
      21804559, 3243768, 18415863, 2769036, 21329840, 19039860, 24338679, 25477664],
    #[15742885, 30968065, 17859023, 14993283, 6712085, 27534882, 5891800, 12866485,
      22796812, 7871879, 22579340, 20744192, 1014723, 17359768, 19888968, 715672,
      22495323, 19693066, 17860177, 18714057, 22153355, 19200963, 18937425, 30303535],
    #[14328470, 29469343, 2507215, 32978222, 23912006, 10418033, 21651573, 15259270,
      22988993, 21920231, 5802124, 19576832, 17459470, 496742, 17829078, 18066534,
      8246632, 453433, 18241105, 20056631, 5148120, 510222, 18232913, 13137199],
    #[13091572, 27151611, 18203721, 29655423, 24969937, 29976008, 16837526, 9554589,
      4474179, 23157614, 20202953, 22706176, 3170570, 21819390, 18000683, 1030142,
      25065204, 3477023, 3477739, 1853205, 17535521, 23699722, 377067, 9735280],
    #[14246744, 9202435, 1937112, 30697628, 19093616, 25343514, 1188848, 9039349,
      5533138, 20220064, 21740309, 19965952, 23556874, 16792576, 6505258, 3195904,
      21391114, 496736, 7400298, 23117674, 20211744, 5182218, 5258090, 30822603],
    #[32961734, 29321646, 18413685, 14837916, 17135728, 12059433, 17502222, 27306603,
      24207231, 20089024, 4660806, 19965952, 6752010, 18877440, 21301066, 54272,
      4592394, 496736, 23117674, 7400298, 20080704, 25130762, 22040426, 32302584],
    #[9336691, 15493996, 4604960, 12579199, 24507089, 16386008, 4259854, 27488026,
      16904916, 20165263, 6991416, 22706176, 6993652, 16781310, 5666100, 3201022,
      19177738, 3477023, 1853205, 3477739, 22641600, 17569524, 6231829, 11005536],
    #[9139678, 29706386, 7767104, 12136735, 24507089, 30638150, 22995952, 9820954,
      17986681, 1855761, 21964949, 24942592, 8384569, 4094, 24780903, 19978238,
      1120199, 18541953, 16777798, 2708920, 24549470, 20553785, 22389318, 25484461],
    #[12398147, 32903537, 2266174, 15838415, 18087494, 30120386, 3472278, 10934842,
      22067422, 1223873, 17622158, 18696192, 17603808, 24163430, 20290590, 7396454,
      17350790, 18188608, 2122182, 277920, 1202430, 1158368, 3981766, 25682029],
    #[29755593, 14841120, 3989217, 25324162, 18955832, 25280909, 3997813, 32669719,
      17584561, 3177100, 19799743, 19105792, 23986000, 22840349, 2133184, 625693,
      24781645, 19876812, 19079297, 3423388, 18520976, 1339216, 20811905, 10548508],
    #[15957508, 33068147, 18628225, 12102577, 3307669, 8962579, 17725144, 31380804,
      234063, 18057281, 20442433, 19240960, 21236942, 21984944, 2137248, 3972784,
      24568446, 2136146, 16826924, 20114588, 18057326, 2981070, 18772524, 25953327],
    #[16195318, 29118940, 3072328, 31866795, 7316622, 8619975, 1334345, 15183166,
      22770743, 19166269, 20558799, 19916800, 19805567, 6057892, 1457296, 18692004,
      3019483, 1506302, 6902053, 22443649, 21131759, 7796095, 8122661, 27071020],
    #[15343206, 32815795, 22804928, 27828839, 3538623, 27426950, 21064143, 9041645,
      23968528, 8061458, 19991924, 24836096, 23978704, 7458196, 2008449, 23524756,
      20035396, 7922584, 18017500, 7915848, 5848913, 2179792, 21716188, 13836581],
    #[32920601, 13823145, 23835267, 10445850, 21354583, 31195981, 3329392, 12477353,
      5288760, 8308794, 20470831, 16992256, 6332859, 4676737, 4960576, 20038785,
      17044794, 3741819, 23704897, 19685824, 25086203, 16888251, 20841793, 29908188]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters00Part08 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters00Part08.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_128 :
    generatedNinthLowerSpinSourceQReplayWord 0 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 0)
    3072 24 0 (prefix_sizes 0) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_129 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3096 3120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_129 :
    generatedNinthLowerSpinSourceQReplayWord 0 129 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 1)
    3096 24 0 (prefix_sizes 1) slice_129
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_130 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3120 3144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_130 :
    generatedNinthLowerSpinSourceQReplayWord 0 130 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 2)
    3120 24 0 (prefix_sizes 2) slice_130
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_131 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3144 3168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_131 :
    generatedNinthLowerSpinSourceQReplayWord 0 131 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 3)
    3144 24 0 (prefix_sizes 3) slice_131
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_132 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3168 3192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_132 :
    generatedNinthLowerSpinSourceQReplayWord 0 132 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 4)
    3168 24 0 (prefix_sizes 4) slice_132
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_133 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3192 3216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_133 :
    generatedNinthLowerSpinSourceQReplayWord 0 133 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 5)
    3192 24 0 (prefix_sizes 5) slice_133
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_134 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3216 3240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_134 :
    generatedNinthLowerSpinSourceQReplayWord 0 134 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 6)
    3216 24 0 (prefix_sizes 6) slice_134
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_135 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3240 3264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_135 :
    generatedNinthLowerSpinSourceQReplayWord 0 135 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 7)
    3240 24 0 (prefix_sizes 7) slice_135
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_136 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3264 3288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_136 :
    generatedNinthLowerSpinSourceQReplayWord 0 136 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 8)
    3264 24 0 (prefix_sizes 8) slice_136
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_137 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3288 3312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_137 :
    generatedNinthLowerSpinSourceQReplayWord 0 137 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 9)
    3288 24 0 (prefix_sizes 9) slice_137
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_138 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3312 3336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_138 :
    generatedNinthLowerSpinSourceQReplayWord 0 138 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 10)
    3312 24 0 (prefix_sizes 10) slice_138
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_139 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3336 3360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_139 :
    generatedNinthLowerSpinSourceQReplayWord 0 139 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 11)
    3336 24 0 (prefix_sizes 11) slice_139
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_140 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3360 3384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_140 :
    generatedNinthLowerSpinSourceQReplayWord 0 140 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 12)
    3360 24 0 (prefix_sizes 12) slice_140
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_141 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3384 3408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_141 :
    generatedNinthLowerSpinSourceQReplayWord 0 141 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 13)
    3384 24 0 (prefix_sizes 13) slice_141
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_142 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3408 3432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_142 :
    generatedNinthLowerSpinSourceQReplayWord 0 142 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 14)
    3408 24 0 (prefix_sizes 14) slice_142
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_143 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3432 3456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_143 :
    generatedNinthLowerSpinSourceQReplayWord 0 143 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 15)
    3432 24 0 (prefix_sizes 15) slice_143
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_144 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3456 3480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_08_144 :
    generatedNinthLowerSpinSourceQReplayWord 0 144 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part08 16)
    3456 24 0 (prefix_sizes 16) slice_144
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords00.extract 128 144 =
      generatedNinthLowerSpinLiteralQReplayLetters00Part08 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_00_part_08 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 0 ⟨128 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters00Part08.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords00
    generatedNinthLowerSpinLiteralQReplayLetters00Part08
    128 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords00.getD (128 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
