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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 : Fin 17 → Array ℕ :=
  ![
    #[29525621, 31861946, 1988465, 8770374, 2768226, 33091690, 721408, 15887092,
      19087151, 23694885, 19056832, 22124544, 19730526, 23624837, 8085185, 19451013,
      5940443, 19607661, 17636534, 1507379, 21540511, 20011102, 19537078, 15262045],
    #[9655258, 9975458, 21510874, 10904010, 6952221, 13213923, 964612, 9034390,
      19419684, 6441770, 18166415, 18384896, 704766, 2146368, 16855688, 704576,
      2341054, 7075100, 5903778, 5486050, 16806518, 6834430, 5297570, 32508929],
    #[29525621, 31861946, 1988465, 8770374, 2768226, 33091690, 721408, 15887092,
      19087151, 23694885, 19056832, 22124544, 19730526, 23624837, 8085185, 19451013,
      5940443, 19607661, 17636534, 1507379, 21540511, 20011102, 19537078, 15262045],
    #[31592981, 16345892, 18126370, 26445606, 3141551, 32999316, 19800269, 31927353,
      52706, 8325669, 18143392, 21067776, 18088896, 25029160, 8085185, 20814376,
      6685160, 3670720, 3439400, 2949376, 6397185, 20859840, 1276712, 12649123],
    #[9712188, 9047595, 22143091, 15221623, 19374513, 25570988, 4635715, 13859393,
      2271283, 20617760, 2193646, 20695040, 16883776, 1676847, 24881177, 6506031,
      24780399, 21215556, 17026859, 198916, 1120345, 20572224, 17461035, 27563495],
    #[25284753, 9787861, 5972256, 31270362, 17711695, 26598401, 23879024, 13859393,
      3057920, 1017997, 20863760, 19789824, 20029472, 16803281, 7917236, 21788113,
      7671281, 22670359, 18909670, 633911, 18136724, 20576288, 19474918, 9707911],
    #[32108029, 32033404, 79139, 13957935, 18442380, 13128029, 5634511, 12574850,
      1167620, 23005382, 20722743, 23894016, 5557287, 20601902, 6054799, 24665134,
      4364297, 1943144, 23586401, 23591503, 23515048, 6435879, 24262241, 11731916],
    #[31791369, 32230545, 2342256, 11450666, 6120905, 30647733, 21486665, 15592903,
      7406340, 8233794, 3330639, 22890496, 18257524, 22683771, 1610180, 22618235,
      200207, 21616376, 19796215, 16842892, 24274864, 24211060, 21262583, 8573248],
    #[32843531, 12812719, 24627663, 32380717, 80661, 31798924, 5891800, 15975195,
      22796812, 20712839, 4802700, 20744192, 23608259, 20937624, 17232712, 20806552,
      497755, 3302922, 22955601, 6610377, 18663563, 21214147, 24000081, 12694913],
    #[15114662, 30646703, 6420943, 12908062, 18574918, 29365313, 21651573, 14697910,
      22988993, 1874407, 21579916, 19576832, 5101838, 3148902, 17405142, 2374758,
      17694056, 19456825, 21526097, 6011447, 1093080, 4223246, 21501521, 29931039],
    #[29737700, 9495787, 16845897, 15499631, 23266001, 31978968, 16837526, 8911501,
      4474179, 4655982, 1582537, 22706176, 19177738, 22730750, 17314603, 18450430,
      8163060, 20555295, 3883243, 17049365, 17154593, 24996106, 757995, 28593248],
    #[27246435, 13791032, 3991256, 13763751, 19216496, 14236193, 1188848, 9200078,
      5533138, 972960, 3463957, 19965952, 4592394, 16806912, 8117034, 19956736,
      6770442, 18828384, 4791146, 5836650, 17668128, 7240458, 6933354, 28585200],
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
      497755, 3302922, 22955601, 6610377, 18663563, 21214147, 24000081, 12694913]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part03 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, true), (13, true), (12, true),
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, true), (12, true), (13, true),
  (13, false), (12, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part03.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_048 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1152 1176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_048 :
    generatedNinthLowerSpinSourceQReplayWord 5 48 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 0)
    1152 24 0 (prefix_sizes 0) slice_048
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_049 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1176 1200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_049 :
    generatedNinthLowerSpinSourceQReplayWord 5 49 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 1)
    1176 24 0 (prefix_sizes 1) slice_049
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_050 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1200 1224 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_050 :
    generatedNinthLowerSpinSourceQReplayWord 5 50 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 2)
    1200 24 0 (prefix_sizes 2) slice_050
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1200 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_051 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1224 1248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_051 :
    generatedNinthLowerSpinSourceQReplayWord 5 51 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 3)
    1224 24 0 (prefix_sizes 3) slice_051
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_052 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1248 1272 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_052 :
    generatedNinthLowerSpinSourceQReplayWord 5 52 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 4)
    1248 24 0 (prefix_sizes 4) slice_052
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1248 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_053 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1272 1296 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_053 :
    generatedNinthLowerSpinSourceQReplayWord 5 53 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 5)
    1272 24 0 (prefix_sizes 5) slice_053
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1272 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_054 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1296 1320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_054 :
    generatedNinthLowerSpinSourceQReplayWord 5 54 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 6)
    1296 24 0 (prefix_sizes 6) slice_054
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_055 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1320 1344 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_055 :
    generatedNinthLowerSpinSourceQReplayWord 5 55 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 7)
    1320 24 0 (prefix_sizes 7) slice_055
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1320 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_056 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1344 1368 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_056 :
    generatedNinthLowerSpinSourceQReplayWord 5 56 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 8)
    1344 24 0 (prefix_sizes 8) slice_056
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1344 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_057 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1368 1392 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_057 :
    generatedNinthLowerSpinSourceQReplayWord 5 57 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 9)
    1368 24 0 (prefix_sizes 9) slice_057
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1368 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_058 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1392 1416 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_058 :
    generatedNinthLowerSpinSourceQReplayWord 5 58 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 10)
    1392 24 0 (prefix_sizes 10) slice_058
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1392 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_059 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1416 1440 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_059 :
    generatedNinthLowerSpinSourceQReplayWord 5 59 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 11)
    1416 24 0 (prefix_sizes 11) slice_059
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1416 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_060 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1440 1464 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_060 :
    generatedNinthLowerSpinSourceQReplayWord 5 60 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 12)
    1440 24 0 (prefix_sizes 12) slice_060
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1440 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_061 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1464 1488 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_061 :
    generatedNinthLowerSpinSourceQReplayWord 5 61 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 13)
    1464 24 0 (prefix_sizes 13) slice_061
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1464 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_062 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1488 1512 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_062 :
    generatedNinthLowerSpinSourceQReplayWord 5 62 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 14)
    1488 24 0 (prefix_sizes 14) slice_062
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1488 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_063 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1512 1536 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_063 :
    generatedNinthLowerSpinSourceQReplayWord 5 63 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 15)
    1512 24 0 (prefix_sizes 15) slice_063
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1512 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_064 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 1536 1560 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_03_064 :
    generatedNinthLowerSpinSourceQReplayWord 5 64 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part03 16)
    1536 24 0 (prefix_sizes 16) slice_064
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (1536 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 48 64 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part03 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_03 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨48 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part03.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part03
    48 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (48 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
