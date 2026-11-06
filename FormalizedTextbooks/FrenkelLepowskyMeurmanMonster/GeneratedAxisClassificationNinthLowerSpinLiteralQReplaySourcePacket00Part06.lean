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
def generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 : Fin 17 → Array ℕ :=
  ![
    #[30203451, 9971224, 5248368, 12368803, 16881097, 15888933, 4709449, 13724247,
      21381711, 5191648, 7037700, 24676352, 24622911, 6547595, 22297645, 21012619,
      5994420, 19693537, 1458261, 16777438, 25158418, 1427263, 8151125, 26941042],
    #[10326599, 28523105, 19907023, 11547875, 23489301, 31691296, 22669016, 25421751,
      18704524, 2619445, 18971148, 22427648, 1849667, 1094600, 19164282, 19790792,
      17740427, 7511354, 4351921, 17161337, 912697, 23218499, 714673, 27508941],
    #[9577913, 9689601, 598479, 9053616, 7134790, 16150669, 4874357, 8409466,
      3901580, 175864, 18000065, 22476800, 3934531, 17822806, 916356, 3451990,
      509205, 21494679, 25065090, 18242260, 154311, 23234883, 20330114, 25227776],
    #[27051916, 14740487, 23635017, 29835651, 8192721, 30945478, 60310, 25206675,
      20047305, 17739274, 3966275, 23091200, 164224, 20066274, 8322757, 792546,
      3425890, 4067071, 20144285, 23259007, 23357253, 18612608, 21991581, 30378248],
    #[29391255, 12417619, 3055320, 30829004, 2316400, 14375746, 17966064, 30408877,
      22440725, 2932564, 8039890, 24463360, 1279437, 274747, 20750873, 17291579,
      3378422, 4474891, 19934461, 2188742, 2908116, 21829069, 17878269, 13584900],
    #[16129527, 27417005, 19789941, 30038175, 358512, 15551266, 725006, 16114272,
      7130694, 20261066, 24088447, 22259712, 2922035, 279867, 18626169, 17931579,
      2804488, 4779352, 18161232, 19006315, 3524682, 23258675, 17165904, 32246985],
    #[29391255, 12417619, 3055320, 30829004, 2316400, 14375746, 17966064, 30408877,
      22440725, 2932564, 8039890, 24463360, 1279437, 274747, 20750873, 17291579,
      3378422, 4474891, 19934461, 2188742, 2908116, 21829069, 17878269, 13584900],
    #[27051916, 14740487, 23635017, 29835651, 8192721, 30945478, 60310, 25206675,
      20047305, 17739274, 3966275, 23091200, 164224, 20066274, 8322757, 792546,
      3425890, 4067071, 20144285, 23259007, 23357253, 18612608, 21991581, 30378248],
    #[9577913, 9689601, 598479, 9053616, 7134790, 16150669, 4874357, 8409466,
      3901580, 175864, 18000065, 22476800, 3934531, 17822806, 916356, 3451990,
      509205, 21494679, 25065090, 18242260, 154311, 23234883, 20330114, 25227776],
    #[10326599, 28523105, 19907023, 11547875, 23489301, 31691296, 22669016, 25421751,
      18704524, 2619445, 18971148, 22427648, 1849667, 1094600, 19164282, 19790792,
      17740427, 7511354, 4351921, 17161337, 912697, 23218499, 714673, 27508941],
    #[30203451, 9971224, 5248368, 12368803, 16881097, 15888933, 4709449, 13724247,
      21381711, 5191648, 7037700, 24676352, 24622911, 6547595, 22297645, 21012619,
      5994420, 19693537, 1458261, 16777438, 25158418, 1427263, 8151125, 26941042],
    #[15886356, 31516358, 5659939, 11419541, 5367948, 13681876, 22411727, 9168139,
      2978871, 4890456, 8085764, 22697984, 17418516, 4732848, 2971938, 18665392,
      21747364, 17926309, 4371969, 18278833, 4864054, 2033940, 4281857, 26801701],
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
      25065204, 3477023, 3477739, 1853205, 17535521, 23699722, 377067, 9735280]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters00Part06 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (13, false),
  (12, true), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters00Part06.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_096 :
    generatedNinthLowerSpinSourceQReplayWord 0 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 0)
    2304 24 0 (prefix_sizes 0) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_097 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2328 2352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_097 :
    generatedNinthLowerSpinSourceQReplayWord 0 97 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 1)
    2328 24 0 (prefix_sizes 1) slice_097
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_098 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2352 2376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_098 :
    generatedNinthLowerSpinSourceQReplayWord 0 98 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 2)
    2352 24 0 (prefix_sizes 2) slice_098
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_099 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2376 2400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_099 :
    generatedNinthLowerSpinSourceQReplayWord 0 99 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 3)
    2376 24 0 (prefix_sizes 3) slice_099
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_100 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2400 2424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_100 :
    generatedNinthLowerSpinSourceQReplayWord 0 100 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 4)
    2400 24 0 (prefix_sizes 4) slice_100
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_101 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2424 2448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_101 :
    generatedNinthLowerSpinSourceQReplayWord 0 101 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 5)
    2424 24 0 (prefix_sizes 5) slice_101
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_102 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2448 2472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_102 :
    generatedNinthLowerSpinSourceQReplayWord 0 102 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 6)
    2448 24 0 (prefix_sizes 6) slice_102
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_103 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2472 2496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_103 :
    generatedNinthLowerSpinSourceQReplayWord 0 103 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 7)
    2472 24 0 (prefix_sizes 7) slice_103
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_104 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2496 2520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_104 :
    generatedNinthLowerSpinSourceQReplayWord 0 104 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 8)
    2496 24 0 (prefix_sizes 8) slice_104
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_105 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2520 2544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_105 :
    generatedNinthLowerSpinSourceQReplayWord 0 105 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 9)
    2520 24 0 (prefix_sizes 9) slice_105
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_106 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2544 2568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_106 :
    generatedNinthLowerSpinSourceQReplayWord 0 106 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 10)
    2544 24 0 (prefix_sizes 10) slice_106
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_107 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2568 2592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_107 :
    generatedNinthLowerSpinSourceQReplayWord 0 107 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 11)
    2568 24 0 (prefix_sizes 11) slice_107
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_108 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2592 2616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_108 :
    generatedNinthLowerSpinSourceQReplayWord 0 108 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 12)
    2592 24 0 (prefix_sizes 12) slice_108
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_109 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2616 2640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_109 :
    generatedNinthLowerSpinSourceQReplayWord 0 109 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 13)
    2616 24 0 (prefix_sizes 13) slice_109
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_110 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2640 2664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_110 :
    generatedNinthLowerSpinSourceQReplayWord 0 110 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 14)
    2640 24 0 (prefix_sizes 14) slice_110
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_111 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2664 2688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_111 :
    generatedNinthLowerSpinSourceQReplayWord 0 111 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 15)
    2664 24 0 (prefix_sizes 15) slice_111
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_00_part_06_112 :
    generatedNinthLowerSpinSourceQReplayWord 0 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords00
    (generatedNinthLowerSpinLiteralQReplayPrefixes00Part06 16)
    2688 24 0 (prefix_sizes 16) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords00.extract 96 112 =
      generatedNinthLowerSpinLiteralQReplayLetters00Part06 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_00_part_06 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 0 ⟨96 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters00Part06.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords00
    generatedNinthLowerSpinLiteralQReplayLetters00Part06
    96 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords00.getD (96 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
