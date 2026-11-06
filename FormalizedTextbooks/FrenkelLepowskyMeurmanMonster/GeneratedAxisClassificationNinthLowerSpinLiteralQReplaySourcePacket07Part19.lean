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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 : Fin 17 → Array ℕ :=
  ![
    #[30530925, 29265304, 24919768, 26079759, 2439280, 15408261, 17966064, 13470562,
      20383696, 17879200, 19162399, 23816192, 25075976, 1431054, 24011044, 19217934,
      21974790, 6490314, 22581196, 4596162, 20879404, 856328, 3704780, 9011958],
    #[14163699, 8579243, 4823157, 11678097, 202864, 13142568, 725006, 13343586,
      17302606, 16834752, 20223359, 22915072, 23213115, 17819453, 4338807, 2047805,
      7326470, 4869972, 21478482, 6620015, 3041356, 2573371, 476242, 26597317],
    #[30530925, 29265304, 24919768, 26079759, 2439280, 15408261, 17966064, 13470562,
      20383696, 17879200, 19162399, 23816192, 25075976, 1431054, 24011044, 19217934,
      21974790, 6490314, 22581196, 4596162, 20879404, 856328, 3704780, 9011958],
    #[14187246, 9940865, 8258633, 13215735, 6488785, 25694272, 60310, 11893479,
      7091785, 19968878, 23210801, 22337536, 17656320, 4837364, 18101025, 17139700,
      20991476, 4979597, 253561, 6162829, 21475617, 5577216, 21759609, 32805272],
    #[31051940, 16372036, 18387407, 12077463, 1797702, 25412544, 4874357, 25965909,
      2603467, 17621479, 18253540, 17283072, 17870852, 2260324, 18021844, 20927844,
      456032, 22300090, 768218, 6188478, 4642256, 3735556, 24293594, 14180479],
    #[33129668, 13992983, 4092367, 29294071, 16857877, 25870430, 22669016, 9659051,
      2219467, 3954055, 3473449, 19367936, 16786436, 19454039, 1591431, 2342999,
      19579987, 22098711, 134980, 8228627, 23737475, 3781636, 24889156, 12730668],
    #[31618173, 29401393, 21280112, 26524051, 22898121, 9421054, 4709449, 13102485,
      24576898, 23366466, 45008, 19134464, 19676914, 19135759, 19092656, 6481167,
      4254717, 18013895, 1277242, 6031413, 6955586, 7827186, 18748730, 15980845],
    #[16761298, 12785376, 21294371, 16494208, 1665164, 28758928, 22411727, 8401788,
      18084425, 6389958, 20729417, 20047872, 4757354, 24182785, 22296480, 7342081,
      3391339, 24447114, 22978529, 882656, 4999370, 23074666, 956385, 31751888],
    #[15528831, 30860333, 22285603, 13528141, 18458764, 28954734, 5634511, 12574850,
      3372617, 25036632, 3996233, 16906240, 21554026, 22295212, 25019454, 4528812,
      19978694, 23875444, 23367346, 20214814, 23400276, 4215658, 2385586, 29461629],
    #[15360404, 31962234, 23192944, 11939032, 8218057, 8720556, 21486665, 15592903,
      21534672, 22745056, 3849090, 19081216, 20327072, 3025126, 16974912, 23748838,
      5749318, 154311, 17901697, 22222951, 7366368, 6879904, 3739777, 31329476],
    #[13489142, 9204421, 401871, 28506917, 4623125, 25674222, 5891800, 15975195,
      24328233, 23371829, 20059595, 17668096, 4227558, 20025189, 2955479, 4552549,
      2217603, 23357253, 6928838, 22908579, 22573361, 19718630, 19407302, 27043358],
    #[32196598, 25953989, 18923983, 10403350, 24915526, 8700707, 21651573, 14697910,
      4218596, 22480632, 19022283, 17532928, 21182251, 17558070, 105956, 4837942,
      20509981, 21553782, 24788843, 4353373, 6386383, 3778347, 3893099, 9877293],
    #[29970176, 16615961, 4338761, 14991983, 22168273, 12705834, 16837526, 8911501,
      4870961, 1971722, 16977481, 18802688, 6098808, 5478938, 6394685, 17998362,
      17591650, 18763423, 22875133, 18651623, 22230085, 21118840, 3073021, 31425654],
    #[12397662, 10595132, 20762328, 14951595, 18225264, 10286633, 1188848, 9200078,
      1903903, 24840020, 7905232, 24004608, 1145799, 17819453, 1879071, 5037885,
      20952314, 24840361, 4621395, 21433198, 17870808, 18103239, 23493715, 27300805],
    #[11808704, 11434146, 2726005, 29925784, 18225264, 25977385, 17502222, 28930915,
      4058495, 5390538, 5733454, 25077760, 18144522, 1431054, 17857868, 24120846,
      16782084, 5787236, 23881056, 5761902, 18860102, 503050, 5021024, 10151670],
    #[12397662, 10595132, 20762328, 14951595, 18225264, 10286633, 1188848, 9200078,
      1903903, 24840020, 7905232, 24004608, 1145799, 17819453, 1879071, 5037885,
      20952314, 24840361, 4621395, 21433198, 17870808, 18103239, 23493715, 27300805],
    #[29970176, 16615961, 4338761, 14991983, 22168273, 12705834, 16837526, 8911501,
      4870961, 1971722, 16977481, 18802688, 6098808, 5478938, 6394685, 17998362,
      17591650, 18763423, 22875133, 18651623, 22230085, 21118840, 3073021, 31425654]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part19 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (13, false),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (13, true), (13, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part19.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_304 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7296 7320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_304 :
    generatedNinthLowerSpinSourceQReplayWord 7 304 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 0)
    7296 24 0 (prefix_sizes 0) slice_304
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_305 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7320 7344 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_305 :
    generatedNinthLowerSpinSourceQReplayWord 7 305 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 1)
    7320 24 0 (prefix_sizes 1) slice_305
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7320 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_306 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7344 7368 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_306 :
    generatedNinthLowerSpinSourceQReplayWord 7 306 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 2)
    7344 24 0 (prefix_sizes 2) slice_306
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7344 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_307 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7368 7392 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_307 :
    generatedNinthLowerSpinSourceQReplayWord 7 307 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 3)
    7368 24 0 (prefix_sizes 3) slice_307
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7368 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_308 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7392 7416 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_308 :
    generatedNinthLowerSpinSourceQReplayWord 7 308 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 4)
    7392 24 0 (prefix_sizes 4) slice_308
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7392 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_309 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7416 7440 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_309 :
    generatedNinthLowerSpinSourceQReplayWord 7 309 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 5)
    7416 24 0 (prefix_sizes 5) slice_309
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7416 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_310 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7440 7464 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_310 :
    generatedNinthLowerSpinSourceQReplayWord 7 310 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 6)
    7440 24 0 (prefix_sizes 6) slice_310
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7440 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_311 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7464 7488 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_311 :
    generatedNinthLowerSpinSourceQReplayWord 7 311 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 7)
    7464 24 0 (prefix_sizes 7) slice_311
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7464 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_312 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7488 7512 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_312 :
    generatedNinthLowerSpinSourceQReplayWord 7 312 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 8)
    7488 24 0 (prefix_sizes 8) slice_312
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7488 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_313 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7512 7536 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_313 :
    generatedNinthLowerSpinSourceQReplayWord 7 313 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 9)
    7512 24 0 (prefix_sizes 9) slice_313
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7512 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_314 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7536 7560 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_314 :
    generatedNinthLowerSpinSourceQReplayWord 7 314 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 10)
    7536 24 0 (prefix_sizes 10) slice_314
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7536 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_315 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7560 7584 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_315 :
    generatedNinthLowerSpinSourceQReplayWord 7 315 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 11)
    7560 24 0 (prefix_sizes 11) slice_315
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7560 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_316 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7584 7608 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_316 :
    generatedNinthLowerSpinSourceQReplayWord 7 316 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 12)
    7584 24 0 (prefix_sizes 12) slice_316
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7584 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_317 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7608 7632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_317 :
    generatedNinthLowerSpinSourceQReplayWord 7 317 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 13)
    7608 24 0 (prefix_sizes 13) slice_317
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_318 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7632 7656 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_318 :
    generatedNinthLowerSpinSourceQReplayWord 7 318 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 14)
    7632 24 0 (prefix_sizes 14) slice_318
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7632 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_319 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7656 7680 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_319 :
    generatedNinthLowerSpinSourceQReplayWord 7 319 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 15)
    7656 24 0 (prefix_sizes 15) slice_319
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7656 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_320 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7680 7704 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_19_320 :
    generatedNinthLowerSpinSourceQReplayWord 7 320 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part19 16)
    7680 24 0 (prefix_sizes 16) slice_320
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7680 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 304 320 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part19 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_19 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨304 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part19.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part19
    304 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (304 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
