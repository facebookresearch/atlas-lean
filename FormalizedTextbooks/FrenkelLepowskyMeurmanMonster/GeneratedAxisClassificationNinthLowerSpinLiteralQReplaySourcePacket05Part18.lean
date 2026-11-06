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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 : Fin 17 → Array ℕ :=
  ![
    #[26661411, 31069522, 1189808, 13492912, 22609016, 32764824, 17369092, 15781890,
      3324779, 20854344, 23138117, 18561024, 18785499, 16782344, 17010475, 7781384,
      24709331, 19351320, 22290379, 22313923, 19923952, 4404443, 22306763, 30252312],
    #[31641302, 32535564, 4140968, 12998746, 7958307, 29874299, 19054860, 12628750,
      18931478, 1828406, 6181575, 20092928, 19179710, 22027762, 2247464, 947698,
      5537100, 20743882, 25090950, 24434292, 4201366, 7874750, 23653254, 11740878],
    #[12932167, 11166974, 5910164, 30224882, 7459108, 29561902, 787212, 14006278,
      1097412, 17091817, 22538100, 18176000, 3000400, 24166242, 2924581, 1906530,
      23248690, 5971063, 74565, 928807, 7753845, 20928592, 3584837, 15140219],
    #[29360577, 30790766, 20305033, 28909724, 4690721, 26996177, 3439368, 32748034,
      22275193, 6810273, 16780331, 18913280, 3852528, 7552281, 19340496, 22275353,
      4230633, 17281232, 5406009, 20787232, 19176480, 19880176, 5123385, 15977436],
    #[13177407, 33306512, 18235940, 10080412, 6136338, 26488367, 19741942, 29995825,
      21013204, 4311713, 19552536, 17860608, 3987696, 4999815, 20393136, 24949383,
      4848247, 17277104, 6097607, 18546752, 17992768, 18827504, 4672199, 32172098],
    #[30053397, 8397996, 23658287, 15249906, 24908861, 32097404, 1869580, 31325471,
      16957311, 17063145, 4253247, 18188288, 2676816, 6994880, 2351239, 16925632,
      8223632, 5311701, 17950533, 306309, 7962839, 20940880, 19097413, 31950219],
    #[32038758, 31991228, 2522488, 30677082, 23734337, 9267659, 18322782, 25560172,
      5516742, 4785718, 19374151, 18384896, 19118270, 1747008, 24160968, 20652096,
      20171006, 1148714, 3375060, 735124, 20978294, 5388478, 2252756, 32233118],
    #[15231846, 14955759, 19531851, 32341956, 7932556, 11349451, 17082355, 8832108,
      24226667, 7713637, 865652, 17344512, 1747744, 1878048, 24317029, 19726368,
      17484544, 17900362, 2811978, 20086890, 23895877, 23849760, 2877514, 31524781],
    #[27505568, 10773816, 20415364, 10774034, 7175361, 28561947, 24442895, 8717808,
      23670703, 2439073, 7949263, 22333440, 6267947, 22701095, 1764351, 93223,
      3000332, 1148551, 7839371, 4319916, 686036, 19698731, 3575435, 12863679],
    #[12226622, 27132011, 18351226, 12490529, 22965772, 10257797, 4782428, 12518595,
      6040930, 19527314, 6056194, 23201792, 5570840, 23462164, 2697554, 772372,
      18548748, 19407129, 23988501, 7530497, 1302602, 19972376, 17819925, 14182796],
    #[12223545, 27149408, 26779760, 4093737, 27175430, 18666887, 17316191, 4142272,
      10287469, 11084447, 18659590, 2230272, 22378768, 6732048, 6943069, 4944156,
      22790144, 2666781, 3037456, 20056065, 1261633, 19968284, 5222673, 26783110],
    #[28281630, 29851167, 30378705, 22282278, 29166086, 5077826, 16779023, 5467505,
      30514448, 26774920, 5157390, 247808, 18053948, 6163260, 16894977, 22331452,
      17735680, 19328961, 6368060, 24348669, 1801277, 5939260, 5455041, 27282623],
    #[9419550, 30309761, 29989585, 5085112, 9920309, 4946722, 17155490, 23883503,
      32328739, 9763003, 22172477, 382976, 17471650, 5314722, 1322668, 6475868,
      19828736, 19676914, 5114018, 7304878, 2649840, 21790812, 23080460, 29015436],
    #[29295673, 26973328, 27111536, 320395, 25799501, 18076965, 2124982, 20915248,
      28421236, 12497876, 20212767, 2562048, 24508896, 6715872, 4519092, 21275070,
      22953984, 16786436, 2824672, 17878458, 18138378, 3858878, 4731994, 11888799],
    #[13771329, 30639264, 11648153, 22268868, 28457094, 20264574, 2669449, 6435918,
      26090187, 11409019, 24198504, 243712, 19762543, 3804527, 1831559, 1353183,
      20873216, 3288658, 253295, 2032525, 6084440, 23959007, 20721378, 12576243],
    #[9181314, 14128316, 9042607, 24474176, 13909959, 23957965, 4489930, 2328793,
      27149893, 16180930, 1990388, 1624064, 22612213, 170229, 3343296, 1125408,
      18423808, 17192170, 2574581, 4210890, 7716832, 18664480, 21137471, 15556871],
    #[10877820, 31954140, 10492241, 23105773, 29845770, 21127731, 5175193, 16780820,
      11022917, 32167825, 17680441, 2676736, 24940120, 130648, 17436766, 2174016,
      19476480, 647956, 134744, 7280468, 6052894, 19586112, 8296716, 32310631]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part18 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, false), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (13, true), (14, false), (12, false), (13, true),
  (12, true), (12, true), (12, true), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part18.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_288 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6912 6936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_288 :
    generatedNinthLowerSpinSourceQReplayWord 5 288 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 0)
    6912 24 0 (prefix_sizes 0) slice_288
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_289 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6936 6960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_289 :
    generatedNinthLowerSpinSourceQReplayWord 5 289 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 1)
    6936 24 0 (prefix_sizes 1) slice_289
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_290 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6960 6984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_290 :
    generatedNinthLowerSpinSourceQReplayWord 5 290 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 2)
    6960 24 0 (prefix_sizes 2) slice_290
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_291 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6984 7008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_291 :
    generatedNinthLowerSpinSourceQReplayWord 5 291 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 3)
    6984 24 0 (prefix_sizes 3) slice_291
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_292 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7008 7032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_292 :
    generatedNinthLowerSpinSourceQReplayWord 5 292 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 4)
    7008 24 0 (prefix_sizes 4) slice_292
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_293 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7032 7056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_293 :
    generatedNinthLowerSpinSourceQReplayWord 5 293 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 5)
    7032 24 0 (prefix_sizes 5) slice_293
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_294 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7056 7080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_294 :
    generatedNinthLowerSpinSourceQReplayWord 5 294 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 6)
    7056 24 0 (prefix_sizes 6) slice_294
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_295 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7080 7104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_295 :
    generatedNinthLowerSpinSourceQReplayWord 5 295 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 7)
    7080 24 0 (prefix_sizes 7) slice_295
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_296 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7104 7128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_296 :
    generatedNinthLowerSpinSourceQReplayWord 5 296 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 8)
    7104 24 0 (prefix_sizes 8) slice_296
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_297 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7128 7152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_297 :
    generatedNinthLowerSpinSourceQReplayWord 5 297 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 9)
    7128 24 0 (prefix_sizes 9) slice_297
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_298 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7152 7176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_298 :
    generatedNinthLowerSpinSourceQReplayWord 5 298 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 10)
    7152 24 0 (prefix_sizes 10) slice_298
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_299 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7176 7200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_299 :
    generatedNinthLowerSpinSourceQReplayWord 5 299 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 11)
    7176 24 0 (prefix_sizes 11) slice_299
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_300 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7200 7224 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_300 :
    generatedNinthLowerSpinSourceQReplayWord 5 300 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 12)
    7200 24 0 (prefix_sizes 12) slice_300
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7200 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_301 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7224 7248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_301 :
    generatedNinthLowerSpinSourceQReplayWord 5 301 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 13)
    7224 24 0 (prefix_sizes 13) slice_301
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_302 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7248 7272 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_302 :
    generatedNinthLowerSpinSourceQReplayWord 5 302 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 14)
    7248 24 0 (prefix_sizes 14) slice_302
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7248 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_303 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7272 7296 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_303 :
    generatedNinthLowerSpinSourceQReplayWord 5 303 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 15)
    7272 24 0 (prefix_sizes 15) slice_303
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7272 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_304 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 7296 7320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_18_304 :
    generatedNinthLowerSpinSourceQReplayWord 5 304 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part18 16)
    7296 24 0 (prefix_sizes 16) slice_304
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (7296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 288 304 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part18 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_18 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨288 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part18.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part18
    288 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (288 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
