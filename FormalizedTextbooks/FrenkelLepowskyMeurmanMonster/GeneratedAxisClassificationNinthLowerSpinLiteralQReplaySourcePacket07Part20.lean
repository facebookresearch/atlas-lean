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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 : Fin 17 → Array ℕ :=
  ![
    #[29970176, 16615961, 4338761, 14991983, 22168273, 12705834, 16837526, 8911501,
      4870961, 1971722, 16977481, 18802688, 6098808, 5478938, 6394685, 17998362,
      17591650, 18763423, 22875133, 18651623, 22230085, 21118840, 3073021, 31425654],
    #[32196598, 25953989, 18923983, 10403350, 24915526, 8700707, 21651573, 14697910,
      4218596, 22480632, 19022283, 17532928, 21182251, 17558070, 105956, 4837942,
      20509981, 21553782, 24788843, 4353373, 6386383, 3778347, 3893099, 9877293],
    #[13489142, 9204421, 401871, 28506917, 4623125, 25674222, 5891800, 15975195,
      24328233, 23371829, 20059595, 17668096, 4227558, 20025189, 2955479, 4552549,
      2217603, 23357253, 6928838, 22908579, 22573361, 19718630, 19407302, 27043358],
    #[15360404, 31962234, 23192944, 11939032, 8218057, 8720556, 21486665, 15592903,
      21534672, 22745056, 3849090, 19081216, 20327072, 3025126, 16974912, 23748838,
      5749318, 154311, 17901697, 22222951, 7366368, 6879904, 3739777, 31329476],
    #[15528831, 30860333, 22285603, 13528141, 18458764, 28954734, 5634511, 12574850,
      3372617, 25036632, 3996233, 16906240, 21554026, 22295212, 25019454, 4528812,
      19978694, 23875444, 23367346, 20214814, 23400276, 4215658, 2385586, 29461629],
    #[31546666, 10588450, 23177504, 28176579, 20005455, 32197103, 23879024, 13859393,
      4729291, 2561290, 23582261, 20064256, 17393899, 3876970, 22830817, 17408106,
      7768193, 18117675, 5346474, 1946816, 6925834, 6322411, 23248042, 13511122],
    #[14826375, 10634127, 5064819, 28430832, 19444145, 32201103, 4635715, 13859393,
      8297931, 18133959, 5333557, 17049600, 19082680, 16949140, 8158849, 3540884,
      4430380, 17309976, 25084724, 1815712, 21359417, 6999480, 7064372, 15534975],
    #[32935096, 12340916, 667170, 30303122, 2555823, 15859376, 19800269, 31927353,
      18387842, 23791480, 18728932, 17512448, 22095264, 19113093, 24576328, 8256645,
      24996133, 3094832, 20002837, 2847888, 8162536, 3081632, 557077, 30635306],
    #[29767896, 28964889, 16838513, 31343506, 2305378, 31591453, 721408, 15887092,
      19415938, 7504006, 3428378, 17639424, 25019635, 2146856, 24880155, 24017448,
      21155547, 19081315, 18120376, 1930384, 4864232, 3355891, 2999992, 15078279],
    #[29285299, 9551553, 5935834, 29938041, 2622749, 12333107, 964612, 9034390,
      24928841, 1864525, 3246642, 21379072, 17127571, 17193001, 4948529, 7032873,
      17479866, 23657746, 20057512, 4627841, 6087330, 8284307, 2778536, 33404088],
    #[29767896, 28964889, 16838513, 31343506, 2305378, 31591453, 721408, 15887092,
      19415938, 7504006, 3428378, 17639424, 25019635, 2146856, 24880155, 24017448,
      21155547, 19081315, 18120376, 1930384, 4864232, 3355891, 2999992, 15078279],
    #[32935096, 12340916, 667170, 30303122, 2555823, 15859376, 19800269, 31927353,
      18387842, 23791480, 18728932, 17512448, 22095264, 19113093, 24576328, 8256645,
      24996133, 3094832, 20002837, 2847888, 8162536, 3081632, 557077, 30635306],
    #[14826375, 10634127, 5064819, 28430832, 19444145, 32201103, 4635715, 13859393,
      8297931, 18133959, 5333557, 17049600, 19082680, 16949140, 8158849, 3540884,
      4430380, 17309976, 25084724, 1815712, 21359417, 6999480, 7064372, 15534975],
    #[31546666, 10588450, 23177504, 28176579, 20005455, 32197103, 23879024, 13859393,
      4729291, 2561290, 23582261, 20064256, 17393899, 3876970, 22830817, 17408106,
      7768193, 18117675, 5346474, 1946816, 6925834, 6322411, 23248042, 13511122],
    #[15528831, 30860333, 22285603, 13528141, 18458764, 28954734, 5634511, 12574850,
      3372617, 25036632, 3996233, 16906240, 21554026, 22295212, 25019454, 4528812,
      19978694, 23875444, 23367346, 20214814, 23400276, 4215658, 2385586, 29461629],
    #[15360404, 31962234, 23192944, 11939032, 8218057, 8720556, 21486665, 15592903,
      21534672, 22745056, 3849090, 19081216, 20327072, 3025126, 16974912, 23748838,
      5749318, 154311, 17901697, 22222951, 7366368, 6879904, 3739777, 31329476],
    #[13489142, 9204421, 401871, 28506917, 4623125, 25674222, 5891800, 15975195,
      24328233, 23371829, 20059595, 17668096, 4227558, 20025189, 2955479, 4552549,
      2217603, 23357253, 6928838, 22908579, 22573361, 19718630, 19407302, 27043358]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part20 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, true), (13, true), (12, true),
  (13, true), (12, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part20.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_320 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7680 7704 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_320 :
    generatedNinthLowerSpinSourceQReplayWord 7 320 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 0)
    7680 24 0 (prefix_sizes 0) slice_320
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7680 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_321 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7704 7728 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_321 :
    generatedNinthLowerSpinSourceQReplayWord 7 321 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 1)
    7704 24 0 (prefix_sizes 1) slice_321
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7704 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_322 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7728 7752 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_322 :
    generatedNinthLowerSpinSourceQReplayWord 7 322 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 2)
    7728 24 0 (prefix_sizes 2) slice_322
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7728 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_323 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7752 7776 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_323 :
    generatedNinthLowerSpinSourceQReplayWord 7 323 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 3)
    7752 24 0 (prefix_sizes 3) slice_323
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7752 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_324 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7776 7800 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_324 :
    generatedNinthLowerSpinSourceQReplayWord 7 324 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 4)
    7776 24 0 (prefix_sizes 4) slice_324
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7776 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_325 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7800 7824 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_325 :
    generatedNinthLowerSpinSourceQReplayWord 7 325 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 5)
    7800 24 0 (prefix_sizes 5) slice_325
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7800 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_326 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7824 7848 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_326 :
    generatedNinthLowerSpinSourceQReplayWord 7 326 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 6)
    7824 24 0 (prefix_sizes 6) slice_326
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7824 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_327 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7848 7872 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_327 :
    generatedNinthLowerSpinSourceQReplayWord 7 327 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 7)
    7848 24 0 (prefix_sizes 7) slice_327
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7848 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_328 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7872 7896 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_328 :
    generatedNinthLowerSpinSourceQReplayWord 7 328 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 8)
    7872 24 0 (prefix_sizes 8) slice_328
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7872 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_329 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7896 7920 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_329 :
    generatedNinthLowerSpinSourceQReplayWord 7 329 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 9)
    7896 24 0 (prefix_sizes 9) slice_329
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7896 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_330 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7920 7944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_330 :
    generatedNinthLowerSpinSourceQReplayWord 7 330 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 10)
    7920 24 0 (prefix_sizes 10) slice_330
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_331 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7944 7968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_331 :
    generatedNinthLowerSpinSourceQReplayWord 7 331 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 11)
    7944 24 0 (prefix_sizes 11) slice_331
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_332 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7968 7992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_332 :
    generatedNinthLowerSpinSourceQReplayWord 7 332 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 12)
    7968 24 0 (prefix_sizes 12) slice_332
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_333 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 7992 8016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_333 :
    generatedNinthLowerSpinSourceQReplayWord 7 333 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 13)
    7992 24 0 (prefix_sizes 13) slice_333
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (7992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_334 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8016 8040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_334 :
    generatedNinthLowerSpinSourceQReplayWord 7 334 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 14)
    8016 24 0 (prefix_sizes 14) slice_334
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_335 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8040 8064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_335 :
    generatedNinthLowerSpinSourceQReplayWord 7 335 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 15)
    8040 24 0 (prefix_sizes 15) slice_335
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_336 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8064 8088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_20_336 :
    generatedNinthLowerSpinSourceQReplayWord 7 336 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part20 16)
    8064 24 0 (prefix_sizes 16) slice_336
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 320 336 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part20 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_20 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨320 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part20.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part20
    320 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (320 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
