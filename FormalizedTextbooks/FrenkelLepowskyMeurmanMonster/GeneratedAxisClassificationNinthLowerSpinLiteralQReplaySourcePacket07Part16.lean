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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 : Fin 17 → Array ℕ :=
  ![
    #[26656278, 31699945, 4619498, 8899875, 7652937, 14710422, 16780355, 9879061,
      5617928, 5227020, 17991970, 5632000, 7974370, 22345346, 117805, 3714,
      16843616, 4682368, 2884064, 4185954, 16779727, 4683234, 20498912, 14383623],
    #[25288392, 25644375, 20842066, 14473504, 6826443, 10243975, 5185741, 15807035,
      5026304, 17214212, 17608995, 360448, 6777938, 19011003, 19454242, 6725051,
      18387433, 21578059, 4919458, 24063257, 6937968, 2098258, 17606818, 9172475],
    #[10651749, 28440919, 19068673, 30808179, 8302027, 12572970, 22729216, 16291269,
      4808909, 17374458, 19693859, 1290240, 6848460, 20070843, 20654991, 7346619,
      1123959, 22013259, 6431548, 7764615, 22350915, 4192204, 17132348, 25923995],
    #[10745616, 27421955, 7381003, 30567970, 22328194, 15747887, 16779268, 15489932,
      923250, 18683234, 20657886, 1548288, 21007993, 374445, 19605172, 22056621,
      21704916, 2425549, 6713881, 2563252, 3768525, 18617977, 20290073, 13757580],
    #[10651749, 28440919, 19068673, 30808179, 8302027, 12572970, 22729216, 16291269,
      4808909, 17374458, 19693859, 1290240, 6848460, 20070843, 20654991, 7346619,
      1123959, 22013259, 6431548, 7764615, 22350915, 4192204, 17132348, 25923995],
    #[25288392, 25644375, 20842066, 14473504, 6826443, 10243975, 5185741, 15807035,
      5026304, 17214212, 17608995, 360448, 6777938, 19011003, 19454242, 6725051,
      18387433, 21578059, 4919458, 24063257, 6937968, 2098258, 17606818, 9172475],
    #[26656278, 31699945, 4619498, 8899875, 7652937, 14710422, 16780355, 9879061,
      5617928, 5227020, 17991970, 5632000, 7974370, 22345346, 117805, 3714,
      16843616, 4682368, 2884064, 4185954, 16779727, 4683234, 20498912, 14383623],
    #[10144549, 15718074, 22620948, 8510755, 24425033, 16573349, 1719664, 9489013,
      8334395, 5030081, 1526671, 5447680, 6983471, 6219697, 20238048, 18673585,
      3027102, 24420429, 2494675, 986978, 448975, 4486959, 17094867, 14945689],
    #[28787492, 32889729, 18193975, 14763376, 21382018, 32638957, 18938319, 28830366,
      5954383, 21638467, 5683652, 4669440, 23047544, 19117444, 4499761, 2145668,
      21266684, 1171594, 21971062, 658930, 16817225, 20002168, 7071862, 27194283],
    #[29959723, 31467978, 23581511, 29106639, 1244619, 8713274, 3145, 9130484,
      481672, 19899858, 21355336, 7794688, 4575951, 19733407, 20139031, 3085215,
      24441168, 3229383, 4712343, 25608, 3086040, 5999311, 22847383, 11974627],
    #[32990844, 28457798, 20863624, 12956745, 20173339, 33484352, 25032408, 13194068,
      21907149, 22396975, 1630089, 2613248, 21513285, 2905599, 906856, 24071679,
      6511034, 4614935, 18137773, 7003986, 18156077, 20761669, 2452141, 26747956],
    #[29652145, 10776358, 1907781, 15135364, 1869189, 31263981, 5795957, 30807242,
      7898829, 5882140, 150234, 3653632, 22921864, 1873311, 1609893, 23678367,
      21372695, 6499770, 1360557, 8191794, 1378861, 18844296, 20269741, 28880980],
    #[26949000, 29670263, 5474264, 9977793, 4707984, 29592630, 301974, 14204432,
      24359193, 1087, 23299953, 6606848, 1838785, 1622181, 2320353, 24447141,
      20063844, 20968333, 19150313, 19590476, 4251936, 6813377, 8023529, 11410110],
    #[11659935, 32236180, 561961, 32088349, 17018280, 32122688, 23393264, 31136097,
      17339184, 588111, 5944776, 6397952, 21035033, 5343201, 24282426, 20922337,
      24942584, 23445706, 3393330, 2762963, 2774307, 19791897, 17260338, 28237267],
    #[28846337, 30323801, 17962522, 31482499, 17422587, 32752862, 5050382, 31726335,
      3641518, 18745679, 24129691, 6381568, 4558516, 5998258, 7861143, 17166002,
      5570566, 24942420, 333650, 399840, 681251, 3905204, 20422482, 25755091],
    #[25208817, 30221055, 19662280, 8629688, 23211361, 28024399, 21303310, 25648233,
      19682144, 17339455, 3513472, 6017024, 5213864, 23588010, 7399304, 672938,
      19495426, 3290634, 7781384, 4966562, 786720, 7927464, 23917576, 10939070],
    #[28997282, 29503841, 409755, 11135211, 8199935, 27549105, 5030896, 25356996,
      19218590, 3298572, 3378304, 6094848, 6031365, 4766516, 21971062, 19120948,
      20290353, 20484921, 7735304, 5434172, 19279987, 8081413, 23744520, 29023213]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part16 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, false), (12, false), (12, true),
  (13, true), (12, true), (13, true), (12, true),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (13, true), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part16.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_256 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6144 6168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_256 :
    generatedNinthLowerSpinSourceQReplayWord 7 256 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 0)
    6144 24 0 (prefix_sizes 0) slice_256
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_257 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6168 6192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_257 :
    generatedNinthLowerSpinSourceQReplayWord 7 257 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 1)
    6168 24 0 (prefix_sizes 1) slice_257
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_258 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6192 6216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_258 :
    generatedNinthLowerSpinSourceQReplayWord 7 258 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 2)
    6192 24 0 (prefix_sizes 2) slice_258
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_259 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6216 6240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_259 :
    generatedNinthLowerSpinSourceQReplayWord 7 259 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 3)
    6216 24 0 (prefix_sizes 3) slice_259
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_260 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6240 6264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_260 :
    generatedNinthLowerSpinSourceQReplayWord 7 260 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 4)
    6240 24 0 (prefix_sizes 4) slice_260
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_261 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6264 6288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_261 :
    generatedNinthLowerSpinSourceQReplayWord 7 261 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 5)
    6264 24 0 (prefix_sizes 5) slice_261
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_262 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6288 6312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_262 :
    generatedNinthLowerSpinSourceQReplayWord 7 262 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 6)
    6288 24 0 (prefix_sizes 6) slice_262
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_263 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6312 6336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_263 :
    generatedNinthLowerSpinSourceQReplayWord 7 263 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 7)
    6312 24 0 (prefix_sizes 7) slice_263
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_264 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6336 6360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_264 :
    generatedNinthLowerSpinSourceQReplayWord 7 264 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 8)
    6336 24 0 (prefix_sizes 8) slice_264
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_265 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6360 6384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_265 :
    generatedNinthLowerSpinSourceQReplayWord 7 265 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 9)
    6360 24 0 (prefix_sizes 9) slice_265
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_266 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6384 6408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_266 :
    generatedNinthLowerSpinSourceQReplayWord 7 266 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 10)
    6384 24 0 (prefix_sizes 10) slice_266
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_267 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6408 6432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_267 :
    generatedNinthLowerSpinSourceQReplayWord 7 267 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 11)
    6408 24 0 (prefix_sizes 11) slice_267
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_268 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6432 6456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_268 :
    generatedNinthLowerSpinSourceQReplayWord 7 268 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 12)
    6432 24 0 (prefix_sizes 12) slice_268
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_269 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6456 6480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_269 :
    generatedNinthLowerSpinSourceQReplayWord 7 269 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 13)
    6456 24 0 (prefix_sizes 13) slice_269
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_270 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6480 6504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_270 :
    generatedNinthLowerSpinSourceQReplayWord 7 270 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 14)
    6480 24 0 (prefix_sizes 14) slice_270
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_271 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6504 6528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_271 :
    generatedNinthLowerSpinSourceQReplayWord 7 271 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 15)
    6504 24 0 (prefix_sizes 15) slice_271
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_272 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6528 6552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_16_272 :
    generatedNinthLowerSpinSourceQReplayWord 7 272 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part16 16)
    6528 24 0 (prefix_sizes 16) slice_272
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 256 272 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_16 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨256 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part16.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part16
    256 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (256 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
