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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 : Fin 17 → Array ℕ :=
  ![
    #[11531169, 25438043, 17237681, 16234531, 23738399, 25327574, 22542040, 31662257,
      23297053, 18558198, 18408211, 311296, 20980396, 17589295, 17606159, 5315631,
      1875587, 20978703, 4813452, 5869219, 22080675, 17156780, 18635404, 11688063],
    #[11382253, 16122849, 21912704, 28915750, 6650170, 8786727, 7596589, 12624346,
      17976422, 1267468, 23879734, 7081984, 2447590, 20309364, 18694235, 4939124,
      3655058, 4780371, 6124737, 25102773, 21868733, 24806, 18169025, 28707224],
    #[8556147, 14430898, 22985856, 11952056, 24129431, 10716650, 24324653, 13887351,
      17501080, 1737970, 24508328, 8052736, 17567512, 4145223, 71016, 23136327,
      1324895, 8270163, 22967820, 5676619, 21918320, 18822936, 1506828, 9071787],
    #[25399768, 12053332, 21726897, 30272932, 4864118, 28634718, 6878936, 8859864,
      24658043, 1460078, 19539604, 806912, 23363274, 16803391, 537631, 3079743,
      20234485, 17067023, 18009338, 4379333, 3429077, 22734538, 7922938, 16394863],
    #[12186763, 25713866, 22783665, 32999671, 21208968, 9371405, 23810165, 10970296,
      5424424, 19289966, 18845785, 1728512, 23989145, 20555201, 19055948, 3608001,
      19367512, 1613148, 18574084, 23221957, 18093781, 23102361, 7836420, 30738929],
    #[10145690, 15087120, 22801536, 28188241, 21363607, 10604625, 21265302, 29778823,
      20322929, 18502898, 5076657, 8036352, 1351409, 1069077, 2494675, 21731349,
      17184484, 6092008, 7053836, 6883865, 22144546, 489201, 17185292, 26160219],
    #[28997282, 29503841, 409755, 11135211, 8199935, 27549105, 5030896, 25356996,
      19218590, 3298572, 3378304, 6094848, 6031365, 4766516, 21971062, 19120948,
      20290353, 20484921, 7735304, 5434172, 19279987, 8081413, 23744520, 29023213],
    #[25208817, 30221055, 19662280, 8629688, 23211361, 28024399, 21303310, 25648233,
      19682144, 17339455, 3513472, 6017024, 5213864, 23588010, 7399304, 672938,
      19495426, 3290634, 7781384, 4966562, 786720, 7927464, 23917576, 10939070],
    #[28846337, 30323801, 17962522, 31482499, 17422587, 32752862, 5050382, 31726335,
      3641518, 18745679, 24129691, 6381568, 4558516, 5998258, 7861143, 17166002,
      5570566, 24942420, 333650, 399840, 681251, 3905204, 20422482, 25755091],
    #[11659935, 32236180, 561961, 32088349, 17018280, 32122688, 23393264, 31136097,
      17339184, 588111, 5944776, 6397952, 21035033, 5343201, 24282426, 20922337,
      24942584, 23445706, 3393330, 2762963, 2774307, 19791897, 17260338, 28237267],
    #[26949000, 29670263, 5474264, 9977793, 4707984, 29592630, 301974, 14204432,
      24359193, 1087, 23299953, 6606848, 1838785, 1622181, 2320353, 24447141,
      20063844, 20968333, 19150313, 19590476, 4251936, 6813377, 8023529, 11410110],
    #[29652145, 10776358, 1907781, 15135364, 1869189, 31263981, 5795957, 30807242,
      7898829, 5882140, 150234, 3653632, 22921864, 1873311, 1609893, 23678367,
      21372695, 6499770, 1360557, 8191794, 1378861, 18844296, 20269741, 28880980],
    #[32990844, 28457798, 20863624, 12956745, 20173339, 33484352, 25032408, 13194068,
      21907149, 22396975, 1630089, 2613248, 21513285, 2905599, 906856, 24071679,
      6511034, 4614935, 18137773, 7003986, 18156077, 20761669, 2452141, 26747956],
    #[29959723, 31467978, 23581511, 29106639, 1244619, 8713274, 3145, 9130484,
      481672, 19899858, 21355336, 7794688, 4575951, 19733407, 20139031, 3085215,
      24441168, 3229383, 4712343, 25608, 3086040, 5999311, 22847383, 11974627],
    #[28787492, 32889729, 18193975, 14763376, 21382018, 32638957, 18938319, 28830366,
      5954383, 21638467, 5683652, 4669440, 23047544, 19117444, 4499761, 2145668,
      21266684, 1171594, 21971062, 658930, 16817225, 20002168, 7071862, 27194283],
    #[10144549, 15718074, 22620948, 8510755, 24425033, 16573349, 1719664, 9489013,
      8334395, 5030081, 1526671, 5447680, 6983471, 6219697, 20238048, 18673585,
      3027102, 24420429, 2494675, 986978, 448975, 4486959, 17094867, 14945689],
    #[26656278, 31699945, 4619498, 8899875, 7652937, 14710422, 16780355, 9879061,
      5617928, 5227020, 17991970, 5632000, 7974370, 22345346, 117805, 3714,
      16843616, 4682368, 2884064, 4185954, 16779727, 4683234, 20498912, 14383623]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part15 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (13, false), (12, false), (12, false), (13, false),
  (12, false), (12, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part15.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_240 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5760 5784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_240 :
    generatedNinthLowerSpinSourceQReplayWord 7 240 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 0)
    5760 24 0 (prefix_sizes 0) slice_240
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_241 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5784 5808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_241 :
    generatedNinthLowerSpinSourceQReplayWord 7 241 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 1)
    5784 24 0 (prefix_sizes 1) slice_241
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_242 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5808 5832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_242 :
    generatedNinthLowerSpinSourceQReplayWord 7 242 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 2)
    5808 24 0 (prefix_sizes 2) slice_242
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_243 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5832 5856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_243 :
    generatedNinthLowerSpinSourceQReplayWord 7 243 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 3)
    5832 24 0 (prefix_sizes 3) slice_243
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_244 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5856 5880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_244 :
    generatedNinthLowerSpinSourceQReplayWord 7 244 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 4)
    5856 24 0 (prefix_sizes 4) slice_244
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_245 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5880 5904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_245 :
    generatedNinthLowerSpinSourceQReplayWord 7 245 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 5)
    5880 24 0 (prefix_sizes 5) slice_245
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_246 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5904 5928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_246 :
    generatedNinthLowerSpinSourceQReplayWord 7 246 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 6)
    5904 24 0 (prefix_sizes 6) slice_246
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_247 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5928 5952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_247 :
    generatedNinthLowerSpinSourceQReplayWord 7 247 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 7)
    5928 24 0 (prefix_sizes 7) slice_247
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_248 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5952 5976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_248 :
    generatedNinthLowerSpinSourceQReplayWord 7 248 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 8)
    5952 24 0 (prefix_sizes 8) slice_248
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_249 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 5976 6000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_249 :
    generatedNinthLowerSpinSourceQReplayWord 7 249 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 9)
    5976 24 0 (prefix_sizes 9) slice_249
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (5976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_250 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6000 6024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_250 :
    generatedNinthLowerSpinSourceQReplayWord 7 250 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 10)
    6000 24 0 (prefix_sizes 10) slice_250
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_251 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6024 6048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_251 :
    generatedNinthLowerSpinSourceQReplayWord 7 251 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 11)
    6024 24 0 (prefix_sizes 11) slice_251
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_252 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6048 6072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_252 :
    generatedNinthLowerSpinSourceQReplayWord 7 252 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 12)
    6048 24 0 (prefix_sizes 12) slice_252
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_253 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6072 6096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_253 :
    generatedNinthLowerSpinSourceQReplayWord 7 253 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 13)
    6072 24 0 (prefix_sizes 13) slice_253
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_254 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6096 6120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_254 :
    generatedNinthLowerSpinSourceQReplayWord 7 254 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 14)
    6096 24 0 (prefix_sizes 14) slice_254
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_255 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6120 6144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_255 :
    generatedNinthLowerSpinSourceQReplayWord 7 255 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 15)
    6120 24 0 (prefix_sizes 15) slice_255
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_256 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6144 6168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_15_256 :
    generatedNinthLowerSpinSourceQReplayWord 7 256 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part15 16)
    6144 24 0 (prefix_sizes 16) slice_256
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 240 256 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_15 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨240 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part15.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part15
    240 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (240 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
