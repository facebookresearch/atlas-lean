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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 : Fin 17 → Array ℕ :=
  ![
    #[14553367, 16149758, 21336352, 31333663, 24228431, 29358557, 18636144, 9480819,
      20198965, 18571405, 22581707, 868352, 23998229, 993277, 25154712, 21901309,
      2961640, 24420429, 2494629, 22466392, 17982349, 21747477, 22657189, 31550959],
    #[29902199, 29998848, 5197939, 29900159, 21541297, 25623075, 420931, 11123181,
      283189, 545312, 25036235, 3883008, 6593094, 18155182, 21983384, 4517550,
      1787112, 4682368, 3364456, 21579974, 20857566, 7823942, 21773928, 29842831],
    #[13842652, 26765302, 407074, 30862032, 6893487, 26298070, 22094029, 15213663,
      19351524, 24343077, 4111234, 6832128, 16882118, 21613722, 6631539, 742554,
      3710300, 21578059, 23923735, 6424717, 3609013, 16777670, 4285463, 11925838],
    #[29694140, 9966582, 20641649, 29694077, 6040930, 27075461, 4510208, 12715372,
      2682906, 6546981, 945026, 4763648, 16973675, 4635492, 21614880, 16970596,
      17062927, 22013259, 24201540, 21096992, 943691, 17000299, 4919620, 8448995],
    #[13224798, 10731924, 7011034, 10538540, 5334301, 11593654, 7845892, 14298387,
      3095090, 20464426, 7641673, 2490368, 17193192, 5722341, 18098733, 21395685,
      17891341, 2425549, 7885504, 1341989, 4348613, 23163112, 22940352, 16542805],
    #[29041503, 29436309, 24703706, 11652653, 7570717, 8644535, 3651588, 12068114,
      8141362, 17384234, 19176009, 2490368, 4675816, 18239717, 17115693, 489701,
      17891341, 20251341, 6838976, 4553253, 17980101, 2126056, 5114560, 29254740],
    #[25373567, 15042997, 6595290, 10548749, 23729437, 11962263, 17741828, 10571058,
      23921202, 20570922, 3996233, 19269632, 21641448, 17709285, 18145837, 2035941,
      17041421, 17083085, 21822144, 24754725, 17756869, 2955496, 6988480, 12043380],
    #[30267796, 25692894, 16977777, 10539349, 19545442, 25494189, 17498624, 31056964,
      23709722, 3286565, 3849090, 21542912, 24788843, 25035620, 23714080, 3820388,
      21242895, 5872971, 2572612, 3103264, 22457931, 8105835, 18684228, 11649739],
    #[14130343, 25435021, 2096674, 9012907, 19918767, 8716973, 3023053, 33140772,
      5681124, 19034661, 2902914, 23611392, 23706054, 6378650, 6621299, 19123354,
      7873884, 8325451, 1831959, 20736141, 23005621, 6826438, 20421655, 26776885],
    #[29977277, 32237770, 2566259, 27421365, 2597297, 27428329, 21412931, 11195943,
      23575093, 4465184, 17978827, 20662272, 7277126, 4476590, 17647768, 18196142,
      4300008, 20597376, 18136680, 4188358, 7858910, 24967750, 7067240, 10799685],
    #[14654141, 32685908, 19736864, 11681461, 934479, 27079287, 7101808, 10838489,
      6364725, 22134925, 16908747, 17647616, 22265621, 25075709, 17509528, 4167677,
      6363368, 1001549, 17946789, 1097560, 5966733, 7753493, 7237797, 28614213],
    #[16761298, 12785376, 21294371, 16494208, 1665164, 28758928, 22411727, 8401788,
      18084425, 6389958, 20729417, 20047872, 4757354, 24182785, 22296480, 7342081,
      3391339, 24447114, 22978529, 882656, 4999370, 23074666, 956385, 31751888],
    #[31618173, 29401393, 21280112, 26524051, 22898121, 9421054, 4709449, 13102485,
      24576898, 23366466, 45008, 19134464, 19676914, 19135759, 19092656, 6481167,
      4254717, 18013895, 1277242, 6031413, 6955586, 7827186, 18748730, 15980845],
    #[33129668, 13992983, 4092367, 29294071, 16857877, 25870430, 22669016, 9659051,
      2219467, 3954055, 3473449, 19367936, 16786436, 19454039, 1591431, 2342999,
      19579987, 22098711, 134980, 8228627, 23737475, 3781636, 24889156, 12730668],
    #[31051940, 16372036, 18387407, 12077463, 1797702, 25412544, 4874357, 25965909,
      2603467, 17621479, 18253540, 17283072, 17870852, 2260324, 18021844, 20927844,
      456032, 22300090, 768218, 6188478, 4642256, 3735556, 24293594, 14180479],
    #[14187246, 9940865, 8258633, 13215735, 6488785, 25694272, 60310, 11893479,
      7091785, 19968878, 23210801, 22337536, 17656320, 4837364, 18101025, 17139700,
      20991476, 4979597, 253561, 6162829, 21475617, 5577216, 21759609, 32805272],
    #[30530925, 29265304, 24919768, 26079759, 2439280, 15408261, 17966064, 13470562,
      20383696, 17879200, 19162399, 23816192, 25075976, 1431054, 24011044, 19217934,
      21974790, 6490314, 22581196, 4596162, 20879404, 856328, 3704780, 9011958]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part18 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (0, false), (5, false), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part18.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_288 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6912 6936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_288 :
    generatedNinthLowerSpinSourceQReplayWord 7 288 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 0)
    6912 24 0 (prefix_sizes 0) slice_288
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_289 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6936 6960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_289 :
    generatedNinthLowerSpinSourceQReplayWord 7 289 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 1)
    6936 24 0 (prefix_sizes 1) slice_289
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_290 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6960 6984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_290 :
    generatedNinthLowerSpinSourceQReplayWord 7 290 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 2)
    6960 24 0 (prefix_sizes 2) slice_290
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_291 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6984 7008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_291 :
    generatedNinthLowerSpinSourceQReplayWord 7 291 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 3)
    6984 24 0 (prefix_sizes 3) slice_291
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_292 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7008 7032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_292 :
    generatedNinthLowerSpinSourceQReplayWord 7 292 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 4)
    7008 24 0 (prefix_sizes 4) slice_292
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_293 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7032 7056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_293 :
    generatedNinthLowerSpinSourceQReplayWord 7 293 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 5)
    7032 24 0 (prefix_sizes 5) slice_293
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_294 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7056 7080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_294 :
    generatedNinthLowerSpinSourceQReplayWord 7 294 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 6)
    7056 24 0 (prefix_sizes 6) slice_294
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_295 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7080 7104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_295 :
    generatedNinthLowerSpinSourceQReplayWord 7 295 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 7)
    7080 24 0 (prefix_sizes 7) slice_295
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_296 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7104 7128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_296 :
    generatedNinthLowerSpinSourceQReplayWord 7 296 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 8)
    7104 24 0 (prefix_sizes 8) slice_296
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_297 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7128 7152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_297 :
    generatedNinthLowerSpinSourceQReplayWord 7 297 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 9)
    7128 24 0 (prefix_sizes 9) slice_297
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_298 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7152 7176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_298 :
    generatedNinthLowerSpinSourceQReplayWord 7 298 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 10)
    7152 24 0 (prefix_sizes 10) slice_298
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_299 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7176 7200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_299 :
    generatedNinthLowerSpinSourceQReplayWord 7 299 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 11)
    7176 24 0 (prefix_sizes 11) slice_299
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_300 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7200 7224 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_300 :
    generatedNinthLowerSpinSourceQReplayWord 7 300 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 12)
    7200 24 0 (prefix_sizes 12) slice_300
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7200 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_301 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7224 7248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_301 :
    generatedNinthLowerSpinSourceQReplayWord 7 301 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 13)
    7224 24 0 (prefix_sizes 13) slice_301
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_302 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7248 7272 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_302 :
    generatedNinthLowerSpinSourceQReplayWord 7 302 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 14)
    7248 24 0 (prefix_sizes 14) slice_302
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7248 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_303 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7272 7296 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_303 :
    generatedNinthLowerSpinSourceQReplayWord 7 303 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 15)
    7272 24 0 (prefix_sizes 15) slice_303
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7272 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_304 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7296 7320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_18_304 :
    generatedNinthLowerSpinSourceQReplayWord 7 304 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part18 16)
    7296 24 0 (prefix_sizes 16) slice_304
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 288 304 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part18 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_18 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨288 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part18.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part18
    288 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (288 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
