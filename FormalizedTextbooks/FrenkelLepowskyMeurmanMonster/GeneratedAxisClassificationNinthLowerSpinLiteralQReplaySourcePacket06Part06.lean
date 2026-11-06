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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 : Fin 17 → Array ℕ :=
  ![
    #[30322051, 27188807, 22697688, 25247192, 18704496, 25941846, 398320, 30035129,
      19485461, 530260, 3122642, 7684096, 18382285, 5392699, 299545, 22126907,
      7212278, 18481163, 3403005, 7658950, 18847700, 21423565, 18023677, 14525968],
    #[16285155, 28789177, 5226613, 10320011, 20662384, 11375414, 17371150, 29964916,
      202310, 19366090, 18638719, 5480448, 18972211, 7523643, 1316473, 23532859,
      5352200, 20338008, 1101392, 22109035, 19923018, 24053299, 16791120, 13128925],
    #[15291311, 8617379, 25152544, 15312816, 21930705, 26901275, 4325390, 33059801,
      7190072, 23450509, 17238740, 5742592, 3318296, 24485916, 917722, 8128540,
      4921860, 20815118, 22005514, 5324566, 23112386, 6335000, 810762, 8594108],
    #[14438754, 11759011, 24067136, 30827566, 21541585, 10034614, 22803440, 12715754,
      22548629, 22614750, 17083513, 5726208, 17290453, 6524956, 3258180, 23738396,
      6184137, 565187, 5223178, 22121238, 8166289, 22219989, 18537226, 8839185],
    #[33220776, 28809657, 6324439, 29190267, 20863088, 12239501, 2326620, 31157055,
      3246077, 50545, 2832068, 7577600, 20578090, 24284475, 19796699, 6772027,
      21801489, 20234259, 711170, 23809849, 20104689, 22189866, 20603394, 31457588],
    #[33551342, 32271326, 17328758, 27583384, 3601561, 9275854, 20398526, 32740625,
      3213313, 2133184, 20248342, 5767168, 18410103, 963147, 7791230, 23386699,
      24268860, 6369338, 16801798, 21740109, 23891977, 23691895, 1075206, 15729432],
    #[9251945, 10138741, 17213087, 28920830, 1426095, 11960646, 3429855, 28339298,
      6546703, 20290590, 8123243, 4812800, 20650896, 18973324, 19219871, 1178252,
      5316892, 6179346, 20978446, 18633090, 17802767, 16778128, 877326, 26597175],
    #[12491460, 27902680, 20935937, 10058750, 17441105, 8779755, 18130399, 26197916,
      5498223, 17604576, 24663494, 7970816, 19015790, 2244673, 19240447, 19015745,
      23932975, 5393185, 7392014, 17408847, 20346257, 20910190, 19612430, 25575930],
    #[15205255, 29662135, 19699727, 15205272, 17567489, 27621799, 4497854, 8752777,
      1610208, 19760984, 1861503, 5791744, 22610415, 6949949, 6232991, 20907069,
      23131602, 5043668, 6, 18388027, 21521008, 18913775, 18388998, 29223568],
    #[28681400, 30320041, 19007475, 13256827, 4474891, 29621917, 23253084, 14048068,
      1392802, 3376394, 461524, 2531328, 8232785, 19466770, 6280580, 6267410,
      18488643, 16844609, 23058946, 2922512, 7357141, 6936401, 4538882, 10476155],
    #[29146540, 32694637, 229531, 14693422, 4067071, 14193016, 5030896, 25356996,
      3113056, 20225776, 20152503, 2211840, 22808827, 16932922, 19957681, 6031418,
      8339649, 8274891, 20517642, 6155056, 1058634, 20087035, 2132746, 32508970],
    #[11959551, 16593651, 18859464, 30398384, 18349409, 31732811, 21303310, 25648233,
      2068576, 3247165, 4142468, 1167360, 21007784, 19654564, 3823234, 4546468,
      23753228, 24896774, 636682, 21235886, 16818986, 20899240, 18890506, 15682484],
    #[26681603, 15623513, 20633114, 32442507, 23337211, 32817110, 5050382, 31726335,
      1413282, 3260481, 3185567, 2519040, 21319352, 1265328, 7815325, 21313200,
      18679816, 20534872, 23404112, 17570016, 4527653, 24401592, 8345168, 8412889],
    #[11604323, 30872231, 2118441, 14003672, 22588840, 12721078, 23393264, 31136097,
      1856316, 262796, 2455858, 3559424, 4257813, 20347933, 7504432, 4256797,
      18574344, 18481397, 24182013, 18491616, 23433765, 6406165, 7120125, 28764889],
    #[11040030, 27979413, 6309848, 15354945, 7763600, 32270932, 301974, 14204432,
      262681, 19808843, 8053267, 6443008, 19664321, 7229491, 17563925, 24315955,
      24425970, 18912623, 21782685, 24352942, 19502292, 18998721, 2226333, 15854666],
    #[30807244, 25860980, 5270597, 9831363, 521605, 13531640, 5795957, 30807242,
      19435205, 93499, 198599, 5632000, 19778176, 7927266, 5567949, 22310370,
      22181730, 25158112, 17241730, 2837344, 1185613, 22344320, 7073410, 11375932],
    #[12985516, 11742346, 23452296, 11739406, 18784795, 13823179, 25032408, 13194068,
      973509, 2570555, 45322, 5447680, 17360973, 23844655, 21698099, 7425839,
      23361378, 24322259, 776113, 3307678, 4073086, 22093901, 23199665, 8873071]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part06 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, false), (13, false), (12, true),
  (12, true), (12, true), (13, false), (12, false),
  (12, false), (12, false), (13, true), (12, true),
  (13, false), (12, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part06.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_096 :
    generatedNinthLowerSpinSourceQReplayWord 6 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 0)
    2304 24 0 (prefix_sizes 0) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_097 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2328 2352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_097 :
    generatedNinthLowerSpinSourceQReplayWord 6 97 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 1)
    2328 24 0 (prefix_sizes 1) slice_097
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_098 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2352 2376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_098 :
    generatedNinthLowerSpinSourceQReplayWord 6 98 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 2)
    2352 24 0 (prefix_sizes 2) slice_098
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_099 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2376 2400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_099 :
    generatedNinthLowerSpinSourceQReplayWord 6 99 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 3)
    2376 24 0 (prefix_sizes 3) slice_099
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_100 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2400 2424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_100 :
    generatedNinthLowerSpinSourceQReplayWord 6 100 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 4)
    2400 24 0 (prefix_sizes 4) slice_100
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_101 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2424 2448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_101 :
    generatedNinthLowerSpinSourceQReplayWord 6 101 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 5)
    2424 24 0 (prefix_sizes 5) slice_101
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_102 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2448 2472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_102 :
    generatedNinthLowerSpinSourceQReplayWord 6 102 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 6)
    2448 24 0 (prefix_sizes 6) slice_102
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_103 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2472 2496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_103 :
    generatedNinthLowerSpinSourceQReplayWord 6 103 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 7)
    2472 24 0 (prefix_sizes 7) slice_103
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_104 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2496 2520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_104 :
    generatedNinthLowerSpinSourceQReplayWord 6 104 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 8)
    2496 24 0 (prefix_sizes 8) slice_104
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_105 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2520 2544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_105 :
    generatedNinthLowerSpinSourceQReplayWord 6 105 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 9)
    2520 24 0 (prefix_sizes 9) slice_105
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_106 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2544 2568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_106 :
    generatedNinthLowerSpinSourceQReplayWord 6 106 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 10)
    2544 24 0 (prefix_sizes 10) slice_106
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_107 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2568 2592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_107 :
    generatedNinthLowerSpinSourceQReplayWord 6 107 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 11)
    2568 24 0 (prefix_sizes 11) slice_107
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_108 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2592 2616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_108 :
    generatedNinthLowerSpinSourceQReplayWord 6 108 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 12)
    2592 24 0 (prefix_sizes 12) slice_108
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_109 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2616 2640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_109 :
    generatedNinthLowerSpinSourceQReplayWord 6 109 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 13)
    2616 24 0 (prefix_sizes 13) slice_109
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_110 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2640 2664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_110 :
    generatedNinthLowerSpinSourceQReplayWord 6 110 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 14)
    2640 24 0 (prefix_sizes 14) slice_110
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_111 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2664 2688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_111 :
    generatedNinthLowerSpinSourceQReplayWord 6 111 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 15)
    2664 24 0 (prefix_sizes 15) slice_111
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_06_112 :
    generatedNinthLowerSpinSourceQReplayWord 6 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part06 16)
    2688 24 0 (prefix_sizes 16) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 96 112 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part06 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_06 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨96 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part06.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part06
    96 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (96 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
