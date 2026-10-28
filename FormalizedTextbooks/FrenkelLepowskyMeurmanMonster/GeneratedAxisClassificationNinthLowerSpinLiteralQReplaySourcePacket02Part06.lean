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
def generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 : Fin 17 → Array ℕ :=
  ![
    #[13225549, 14118510, 5248368, 28629973, 1621449, 15219283, 4709449, 9773601,
      5055055, 4802528, 4066052, 24676352, 24960831, 19376267, 18154541, 17098891,
      18112436, 19468257, 22812757, 921822, 3521298, 18786111, 20330581, 10382852],
    #[15697360, 16045558, 19907023, 11662196, 6697749, 27532727, 22669016, 8525856,
      7055500, 1194037, 17941004, 22427648, 7008579, 23348168, 23549050, 22610888,
      821899, 4545850, 24616881, 4512889, 20452665, 1345859, 20914097, 14749530],
    #[29582467, 13714235, 598479, 11429002, 24946246, 25467319, 4874357, 8656960,
      21858444, 3243768, 17957057, 22476800, 4849987, 5096534, 6824836, 7771222,
      20184341, 23075735, 7188098, 4700884, 17924807, 1345859, 2485890, 31550266],
    #[33498266, 31876881, 23635017, 31683221, 17480401, 32422864, 60310, 31659141,
      7615945, 19693066, 2907459, 23091200, 4675968, 7544802, 6178501, 5058530,
      19967586, 6262527, 5638301, 4634495, 69445, 5886336, 2816157, 9220638],
    #[30555822, 9782634, 3055320, 14696181, 20795504, 33137787, 17966064, 32677780,
      3238677, 134996, 1951186, 24463360, 7638477, 21430587, 23190041, 21291323,
      18330870, 5900299, 677117, 22554054, 18229204, 2758093, 2798845, 28353853],
    #[13164541, 27325351, 19789941, 15108757, 18575472, 13836584, 725006, 16513130,
      17501766, 19630282, 20461439, 22259712, 4939315, 23172411, 21470841, 24397115,
      19452680, 7773528, 2717264, 8106859, 17408074, 337459, 3769936, 28948163],
    #[30555822, 9782634, 3055320, 14696181, 20795504, 33137787, 17966064, 32677780,
      3238677, 134996, 1951186, 24463360, 7638477, 21430587, 23190041, 21291323,
      18330870, 5900299, 677117, 22554054, 18229204, 2758093, 2798845, 28353853],
    #[33498266, 31876881, 23635017, 31683221, 17480401, 32422864, 60310, 31659141,
      7615945, 19693066, 2907459, 23091200, 4675968, 7544802, 6178501, 5058530,
      19967586, 6262527, 5638301, 4634495, 69445, 5886336, 2816157, 9220638],
    #[29582467, 13714235, 598479, 11429002, 24946246, 25467319, 4874357, 8656960,
      21858444, 3243768, 17957057, 22476800, 4849987, 5096534, 6824836, 7771222,
      20184341, 23075735, 7188098, 4700884, 17924807, 1345859, 2485890, 31550266],
    #[15697360, 16045558, 19907023, 11662196, 6697749, 27532727, 22669016, 8525856,
      7055500, 1194037, 17941004, 22427648, 7008579, 23348168, 23549050, 22610888,
      821899, 4545850, 24616881, 4512889, 20452665, 1345859, 20914097, 14749530],
    #[13225549, 14118510, 5248368, 28629973, 1621449, 15219283, 4709449, 9773601,
      5055055, 4802528, 4066052, 24676352, 24960831, 19376267, 18154541, 17098891,
      18112436, 19468257, 22812757, 921822, 3521298, 18786111, 20330581, 10382852],
    #[26036423, 13041173, 5659939, 9310022, 24076428, 8420359, 22411727, 31718872,
      20345911, 6000472, 5818628, 22697984, 18006292, 22615984, 7299362, 17688496,
      4325028, 21141669, 18583041, 6224305, 18022454, 17041684, 18378241, 11722486],
    #[28438004, 15751797, 4238627, 26110758, 7299212, 9095508, 5634511, 13203595,
      20762884, 7473350, 6597687, 23894016, 20468775, 5686318, 6054799, 1360942,
      4364297, 24198760, 753249, 23591503, 677800, 17738791, 2010721, 27827141],
    #[33459974, 31632030, 7361904, 27582245, 18398665, 30452666, 21486665, 11023304,
      25142020, 24314690, 19483215, 22890496, 4972148, 485499, 1610180, 288891,
      200207, 1351416, 7559415, 16842892, 3092400, 2893428, 1652983, 9027407],
    #[27866960, 15974900, 17859023, 14440310, 23474965, 14855895, 5891800, 26303296,
      6668, 6802823, 17875084, 20744192, 5551043, 258968, 17232712, 127896,
      497755, 17755658, 6475345, 6610377, 2113675, 8338371, 5422673, 28503514],
    #[10888398, 13219015, 2507215, 30069622, 8169030, 13494569, 21651573, 27150558,
      3393729, 24222183, 1048716, 19576832, 23552270, 18527334, 17405142, 17728614,
      17694056, 154425, 6475345, 6011447, 20583896, 23775502, 6467153, 27753335],
    #[9077776, 25633311, 18203721, 28841883, 703185, 10189612, 16837526, 30512249,
      17495363, 17415022, 23641545, 22706176, 8313098, 45054, 17314603, 4456446,
      8163060, 6544927, 23148779, 17049365, 6273569, 2560266, 22145259, 30294676]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters02Part06 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (13, false),
  (12, true), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters02Part06.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_096 :
    generatedNinthLowerSpinSourceQReplayWord 2 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 0)
    2304 24 0 (prefix_sizes 0) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_097 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2328 2352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_097 :
    generatedNinthLowerSpinSourceQReplayWord 2 97 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 1)
    2328 24 0 (prefix_sizes 1) slice_097
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_098 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2352 2376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_098 :
    generatedNinthLowerSpinSourceQReplayWord 2 98 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 2)
    2352 24 0 (prefix_sizes 2) slice_098
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_099 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2376 2400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_099 :
    generatedNinthLowerSpinSourceQReplayWord 2 99 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 3)
    2376 24 0 (prefix_sizes 3) slice_099
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_100 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2400 2424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_100 :
    generatedNinthLowerSpinSourceQReplayWord 2 100 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 4)
    2400 24 0 (prefix_sizes 4) slice_100
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_101 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2424 2448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_101 :
    generatedNinthLowerSpinSourceQReplayWord 2 101 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 5)
    2424 24 0 (prefix_sizes 5) slice_101
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_102 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2448 2472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_102 :
    generatedNinthLowerSpinSourceQReplayWord 2 102 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 6)
    2448 24 0 (prefix_sizes 6) slice_102
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_103 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2472 2496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_103 :
    generatedNinthLowerSpinSourceQReplayWord 2 103 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 7)
    2472 24 0 (prefix_sizes 7) slice_103
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_104 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2496 2520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_104 :
    generatedNinthLowerSpinSourceQReplayWord 2 104 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 8)
    2496 24 0 (prefix_sizes 8) slice_104
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_105 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2520 2544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_105 :
    generatedNinthLowerSpinSourceQReplayWord 2 105 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 9)
    2520 24 0 (prefix_sizes 9) slice_105
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_106 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2544 2568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_106 :
    generatedNinthLowerSpinSourceQReplayWord 2 106 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 10)
    2544 24 0 (prefix_sizes 10) slice_106
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_107 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2568 2592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_107 :
    generatedNinthLowerSpinSourceQReplayWord 2 107 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 11)
    2568 24 0 (prefix_sizes 11) slice_107
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_108 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2592 2616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_108 :
    generatedNinthLowerSpinSourceQReplayWord 2 108 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 12)
    2592 24 0 (prefix_sizes 12) slice_108
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_109 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2616 2640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_109 :
    generatedNinthLowerSpinSourceQReplayWord 2 109 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 13)
    2616 24 0 (prefix_sizes 13) slice_109
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_110 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2640 2664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_110 :
    generatedNinthLowerSpinSourceQReplayWord 2 110 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 14)
    2640 24 0 (prefix_sizes 14) slice_110
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_111 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2664 2688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_111 :
    generatedNinthLowerSpinSourceQReplayWord 2 111 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 15)
    2664 24 0 (prefix_sizes 15) slice_111
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords02.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_02_part_06_112 :
    generatedNinthLowerSpinSourceQReplayWord 2 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords02
    (generatedNinthLowerSpinLiteralQReplayPrefixes02Part06 16)
    2688 24 0 (prefix_sizes 16) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords02.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords02.extract 96 112 =
      generatedNinthLowerSpinLiteralQReplayLetters02Part06 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_02_part_06 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 2 ⟨96 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters02Part06.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords02
    generatedNinthLowerSpinLiteralQReplayLetters02Part06
    96 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords02.getD (96 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
