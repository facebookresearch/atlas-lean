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
def generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 : Fin 17 → Array ℕ :=
  ![
    #[30158710, 10357156, 7210275, 14680311, 7299212, 29498294, 5634511, 9921129,
      3568695, 19490648, 5660932, 5918720, 2791700, 7012272, 5519650, 20842416,
      21647012, 17012901, 22101505, 2597297, 17825846, 3952916, 22208001, 26632519],
    #[16120777, 32623594, 7089520, 16090705, 18398665, 30805975, 21486665, 13430693,
      21832271, 19443680, 6669060, 7897088, 4253503, 4669579, 19610669, 23333003,
      4755380, 19402721, 16894037, 3352798, 3652370, 2268991, 23849045, 25355136],
    #[14491215, 14605929, 24066511, 28340459, 23474965, 30774824, 5891800, 30940095,
      23832716, 20750389, 24820236, 5648384, 19532099, 773064, 23379066, 20349896,
      19135115, 281914, 18481073, 4535417, 24839481, 22311235, 22118321, 26143941],
    #[32648625, 14199305, 6891983, 27927992, 8169030, 12583045, 21651573, 30222706,
      5081228, 20961016, 25143489, 5697536, 19532099, 19041366, 8256388, 1692758,
      3980565, 16907159, 200322, 4608724, 23352007, 24412483, 4935298, 25922056],
    #[31569036, 10942215, 24054857, 16394883, 703185, 10349510, 16837526, 13208723,
      24393161, 7845386, 7484739, 6311936, 21033344, 17188834, 3419845, 3702754,
      4349538, 7413503, 682141, 7311231, 7130949, 22968704, 7772317, 13208072],
    #[15972763, 32682591, 7362264, 11510208, 4018288, 11965262, 1188848, 26591393,
      20015893, 23689044, 7040466, 7684096, 19547597, 7485755, 22127129, 24236347,
      8144118, 280587, 4187389, 22588870, 24680404, 24436173, 2032893, 30050824],
    #[32710139, 32346529, 24375413, 28545171, 1798256, 28738350, 17502222, 25567852,
      724550, 4595914, 25055103, 5480448, 18175539, 7507259, 21493369, 23549243,
      6669064, 535896, 1758800, 5966699, 22528074, 22752819, 665168, 14617797],
    #[15972763, 32682591, 7362264, 11510208, 4018288, 11965262, 1188848, 26591393,
      20015893, 23689044, 7040466, 7684096, 19547597, 7485755, 22127129, 24236347,
      8144118, 280587, 4187389, 22588870, 24680404, 24436173, 2032893, 30050824],
    #[31569036, 10942215, 24054857, 16394883, 703185, 10349510, 16837526, 13208723,
      24393161, 7845386, 7484739, 6311936, 21033344, 17188834, 3419845, 3702754,
      4349538, 7413503, 682141, 7311231, 7130949, 22968704, 7772317, 13208072],
    #[32648625, 14199305, 6891983, 27927992, 8169030, 12583045, 21651573, 30222706,
      5081228, 20961016, 25143489, 5697536, 19532099, 19041366, 8256388, 1692758,
      3980565, 16907159, 200322, 4608724, 23352007, 24412483, 4935298, 25922056],
    #[14491215, 14605929, 24066511, 28340459, 23474965, 30774824, 5891800, 30940095,
      23832716, 20750389, 24820236, 5648384, 19532099, 773064, 23379066, 20349896,
      19135115, 281914, 18481073, 4535417, 24839481, 22311235, 22118321, 26143941],
    #[16120777, 32623594, 7089520, 16090705, 18398665, 30805975, 21486665, 13430693,
      21832271, 19443680, 6669060, 7897088, 4253503, 4669579, 19610669, 23333003,
      4755380, 19402721, 16894037, 3352798, 3652370, 2268991, 23849045, 25355136],
    #[30158710, 10357156, 7210275, 14680311, 7299212, 29498294, 5634511, 9921129,
      3568695, 19490648, 5660932, 5918720, 2791700, 7012272, 5519650, 20842416,
      21647012, 17012901, 22101505, 2597297, 17825846, 3952916, 22208001, 26632519],
    #[13273974, 10665207, 7927075, 13256100, 24076428, 16039894, 22411727, 10601993,
      3985668, 20324550, 4863031, 7114752, 3111, 21171246, 6368143, 66606,
      24053769, 18931304, 7802465, 17711695, 1001384, 3601447, 6479457, 26264903],
    #[13303707, 13408771, 5008752, 32020408, 1621449, 31705895, 4709449, 33106773,
      8364804, 3615554, 24576591, 6111232, 24634996, 23531643, 2341316, 6559867,
      23023119, 3198712, 739575, 18442380, 2637744, 17833588, 6367479, 12445650],
    #[14490541, 11889929, 22051279, 31753099, 6697749, 30573098, 22669016, 14618557,
      16783884, 19129735, 19810444, 3964928, 18107331, 20880280, 16911176, 3969944,
      24774747, 24620554, 6692433, 6120905, 6570123, 20956099, 5664337, 26143015],
    #[13752990, 25877143, 4606415, 14103846, 24946246, 30996345, 4874357, 14016142,
      20170945, 225767, 3049612, 2797568, 485646, 3271782, 17530070, 19256422,
      4631912, 6023993, 7351889, 6423095, 22607320, 704782, 7360081, 27819303]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters04Part06 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (13, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (13, false), (12, true), (12, true), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters04Part06.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_096 :
    generatedNinthLowerSpinSourceQReplayWord 4 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 0)
    2304 24 0 (prefix_sizes 0) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_097 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2328 2352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_097 :
    generatedNinthLowerSpinSourceQReplayWord 4 97 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 1)
    2328 24 0 (prefix_sizes 1) slice_097
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_098 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2352 2376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_098 :
    generatedNinthLowerSpinSourceQReplayWord 4 98 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 2)
    2352 24 0 (prefix_sizes 2) slice_098
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_099 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2376 2400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_099 :
    generatedNinthLowerSpinSourceQReplayWord 4 99 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 3)
    2376 24 0 (prefix_sizes 3) slice_099
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_100 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2400 2424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_100 :
    generatedNinthLowerSpinSourceQReplayWord 4 100 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 4)
    2400 24 0 (prefix_sizes 4) slice_100
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_101 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2424 2448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_101 :
    generatedNinthLowerSpinSourceQReplayWord 4 101 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 5)
    2424 24 0 (prefix_sizes 5) slice_101
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_102 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2448 2472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_102 :
    generatedNinthLowerSpinSourceQReplayWord 4 102 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 6)
    2448 24 0 (prefix_sizes 6) slice_102
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_103 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2472 2496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_103 :
    generatedNinthLowerSpinSourceQReplayWord 4 103 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 7)
    2472 24 0 (prefix_sizes 7) slice_103
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_104 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2496 2520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_104 :
    generatedNinthLowerSpinSourceQReplayWord 4 104 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 8)
    2496 24 0 (prefix_sizes 8) slice_104
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_105 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2520 2544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_105 :
    generatedNinthLowerSpinSourceQReplayWord 4 105 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 9)
    2520 24 0 (prefix_sizes 9) slice_105
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_106 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2544 2568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_106 :
    generatedNinthLowerSpinSourceQReplayWord 4 106 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 10)
    2544 24 0 (prefix_sizes 10) slice_106
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_107 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2568 2592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_107 :
    generatedNinthLowerSpinSourceQReplayWord 4 107 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 11)
    2568 24 0 (prefix_sizes 11) slice_107
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_108 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2592 2616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_108 :
    generatedNinthLowerSpinSourceQReplayWord 4 108 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 12)
    2592 24 0 (prefix_sizes 12) slice_108
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_109 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2616 2640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_109 :
    generatedNinthLowerSpinSourceQReplayWord 4 109 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 13)
    2616 24 0 (prefix_sizes 13) slice_109
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_110 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2640 2664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_110 :
    generatedNinthLowerSpinSourceQReplayWord 4 110 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 14)
    2640 24 0 (prefix_sizes 14) slice_110
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_111 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2664 2688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_111 :
    generatedNinthLowerSpinSourceQReplayWord 4 111 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 15)
    2664 24 0 (prefix_sizes 15) slice_111
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_06_112 :
    generatedNinthLowerSpinSourceQReplayWord 4 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part06 16)
    2688 24 0 (prefix_sizes 16) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords04.extract 96 112 =
      generatedNinthLowerSpinLiteralQReplayLetters04Part06 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_04_part_06 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 4 ⟨96 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters04Part06.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords04
    generatedNinthLowerSpinLiteralQReplayLetters04Part06
    96 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords04.getD (96 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
