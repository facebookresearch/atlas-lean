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
def generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 : Fin 17 → Array ℕ :=
  ![
    #[13091572, 27151611, 18203721, 29655423, 24969937, 29976008, 16837526, 9554589,
      4474179, 23157614, 20202953, 22706176, 3170570, 21819390, 18000683, 1030142,
      25065204, 3477023, 3477739, 1853205, 17535521, 23699722, 377067, 9735280],
    #[14246744, 9202435, 1937112, 30697628, 19093616, 25343514, 1188848, 9039349,
      5533138, 20220064, 21740309, 19965952, 23556874, 16792576, 6505258, 3195904,
      21391114, 496736, 7400298, 23117674, 20211744, 5182218, 5258090, 30822603],
    #[32961734, 29321646, 18413685, 14837916, 17135728, 12059433, 17502222, 27306603,
      24207231, 20089024, 4660806, 19965952, 6752010, 18877440, 21301066, 54272,
      4592394, 496736, 23117674, 7400298, 20080704, 25130762, 22040426, 32302584],
    #[14246744, 9202435, 1937112, 30697628, 19093616, 25343514, 1188848, 9039349,
      5533138, 20220064, 21740309, 19965952, 23556874, 16792576, 6505258, 3195904,
      21391114, 496736, 7400298, 23117674, 20211744, 5182218, 5258090, 30822603],
    #[13091572, 27151611, 18203721, 29655423, 24969937, 29976008, 16837526, 9554589,
      4474179, 23157614, 20202953, 22706176, 3170570, 21819390, 18000683, 1030142,
      25065204, 3477023, 3477739, 1853205, 17535521, 23699722, 377067, 9735280],
    #[14328470, 29469343, 2507215, 32978222, 23912006, 10418033, 21651573, 15259270,
      22988993, 21920231, 5802124, 19576832, 17459470, 496742, 17829078, 18066534,
      8246632, 453433, 18241105, 20056631, 5148120, 510222, 18232913, 13137199],
    #[15742885, 30968065, 17859023, 14993283, 6712085, 27534882, 5891800, 12866485,
      22796812, 7871879, 22579340, 20744192, 1014723, 17359768, 19888968, 715672,
      22495323, 19693066, 17860177, 18714057, 22153355, 19200963, 18937425, 30303535],
    #[13830761, 27621361, 7361904, 27372106, 103881, 31631061, 21486665, 12697255,
      7406340, 24486722, 24928847, 22890496, 4552308, 21395579, 8153540, 4550779,
      21804559, 3243768, 18415863, 2769036, 21329840, 19039860, 24338679, 25477664],
    #[12852244, 31216533, 4238627, 8682182, 22145164, 14725300, 5634511, 29069675,
      1167620, 5441734, 5321783, 23894016, 18177063, 22529070, 2661263, 1428526,
      24023049, 17092200, 22185569, 4131407, 22261672, 2337831, 21452385, 11436581],
    #[31970754, 31188102, 7543072, 26955913, 23355983, 16107858, 23879024, 13733650,
      3057920, 21727373, 7637776, 19789824, 1675296, 23895505, 3966644, 2131409,
      20039153, 7427095, 21821926, 17378359, 24694420, 17940512, 21322214, 9979092],
    #[13948783, 31609720, 22669427, 11068964, 21713329, 12639231, 4635715, 13733650,
      2271283, 5798432, 23951598, 20695040, 630848, 7585327, 20525081, 17393199,
      1586799, 7012676, 21585707, 19118340, 5998681, 20045888, 21036843, 11071668],
    #[10607076, 30636245, 18390562, 29785303, 5709743, 32529509, 19800269, 15198152,
      52706, 22014501, 2082976, 21067776, 1573824, 25035304, 1140417, 4094504,
      23718376, 22141632, 5393192, 21549312, 503041, 20071360, 7686952, 10545490],
    #[9264343, 31514136, 1331057, 31209956, 6430050, 31836872, 721408, 16277590,
      19087151, 7953957, 4188352, 22124544, 2555998, 25011333, 2598593, 4004997,
      21327067, 6428781, 22805686, 22294579, 18763423, 20660318, 24968374, 10697727],
    #[27976638, 14724806, 21504730, 27804078, 6960413, 15761543, 964612, 29780722,
      19419684, 23259946, 6533775, 18384896, 17486078, 2713664, 21609096, 16998464,
      19529918, 19586332, 1213858, 17991138, 21553782, 6836478, 1590690, 25279589],
    #[9264343, 31514136, 1331057, 31209956, 6430050, 31836872, 721408, 16277590,
      19087151, 7953957, 4188352, 22124544, 2555998, 25011333, 2598593, 4004997,
      21327067, 6428781, 22805686, 22294579, 18763423, 20660318, 24968374, 10697727],
    #[10607076, 30636245, 18390562, 29785303, 5709743, 32529509, 19800269, 15198152,
      52706, 22014501, 2082976, 21067776, 1573824, 25035304, 1140417, 4094504,
      23718376, 22141632, 5393192, 21549312, 503041, 20071360, 7686952, 10545490],
    #[13948783, 31609720, 22669427, 11068964, 21713329, 12639231, 4635715, 13733650,
      2271283, 5798432, 23951598, 20695040, 630848, 7585327, 20525081, 17393199,
      1586799, 7012676, 21585707, 19118340, 5998681, 20045888, 21036843, 11071668]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters00Part07 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters00Part07.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_112 :
    generatedNinthLowerSpinSourceQReplayWord 0 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 0)
    2688 24 0 (prefix_sizes 0) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_113 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2712 2736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_113 :
    generatedNinthLowerSpinSourceQReplayWord 0 113 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 1)
    2712 24 0 (prefix_sizes 1) slice_113
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_114 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2736 2760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_114 :
    generatedNinthLowerSpinSourceQReplayWord 0 114 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 2)
    2736 24 0 (prefix_sizes 2) slice_114
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_115 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2760 2784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_115 :
    generatedNinthLowerSpinSourceQReplayWord 0 115 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 3)
    2760 24 0 (prefix_sizes 3) slice_115
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_116 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2784 2808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_116 :
    generatedNinthLowerSpinSourceQReplayWord 0 116 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 4)
    2784 24 0 (prefix_sizes 4) slice_116
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_117 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2808 2832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_117 :
    generatedNinthLowerSpinSourceQReplayWord 0 117 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 5)
    2808 24 0 (prefix_sizes 5) slice_117
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_118 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2832 2856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_118 :
    generatedNinthLowerSpinSourceQReplayWord 0 118 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 6)
    2832 24 0 (prefix_sizes 6) slice_118
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_119 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2856 2880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_119 :
    generatedNinthLowerSpinSourceQReplayWord 0 119 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 7)
    2856 24 0 (prefix_sizes 7) slice_119
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_120 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2880 2904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_120 :
    generatedNinthLowerSpinSourceQReplayWord 0 120 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 8)
    2880 24 0 (prefix_sizes 8) slice_120
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_121 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2904 2928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_121 :
    generatedNinthLowerSpinSourceQReplayWord 0 121 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 9)
    2904 24 0 (prefix_sizes 9) slice_121
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_122 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2928 2952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_122 :
    generatedNinthLowerSpinSourceQReplayWord 0 122 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 10)
    2928 24 0 (prefix_sizes 10) slice_122
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_123 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2952 2976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_123 :
    generatedNinthLowerSpinSourceQReplayWord 0 123 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 11)
    2952 24 0 (prefix_sizes 11) slice_123
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_124 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2976 3000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_124 :
    generatedNinthLowerSpinSourceQReplayWord 0 124 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 12)
    2976 24 0 (prefix_sizes 12) slice_124
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_125 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3000 3024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_125 :
    generatedNinthLowerSpinSourceQReplayWord 0 125 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 13)
    3000 24 0 (prefix_sizes 13) slice_125
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_126 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3024 3048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_126 :
    generatedNinthLowerSpinSourceQReplayWord 0 126 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 14)
    3024 24 0 (prefix_sizes 14) slice_126
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_127 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3048 3072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_127 :
    generatedNinthLowerSpinSourceQReplayWord 0 127 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 15)
    3048 24 0 (prefix_sizes 15) slice_127
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_128 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 3072 3096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_07_128 :
    generatedNinthLowerSpinSourceQReplayWord 0 128 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part07 16)
    3072 24 0 (prefix_sizes 16) slice_128
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (3072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords00.extract 112 128 =
      generatedNinthLowerSpinLiteralQReplayLetters00Part07 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_00_part_07 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 0 ⟨112 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters00Part07.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords00
    generatedNinthLowerSpinLiteralQReplayLetters00Part07
    112 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords00.getD (112 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
