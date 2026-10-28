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
def generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 : Fin 17 → Array ℕ :=
  ![
    #[1, 2, 4, 8, 16, 32, 64, 128,
      256, 512, 1024, 2048, 4096, 8192, 16384, 32768,
      65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608],
    #[67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856,
      811264, 311808, 1024, 2048, 4096, 8192, 16384, 32768,
      65536, 16910336, 262144, 524288, 1048576, 2097152, 4194304, 8450080],
    #[129021, 633614, 1224972, 5898764, 4989744, 2550305, 6648768, 1657167,
      1163276, 3651588, 51198, 2048, 987136, 4403200, 1454080, 2699264,
      4259840, 16975872, 4718592, 786432, 3190784, 49152, 5181440, 15342113],
    #[20082837, 6774790, 23487244, 16784132, 1159449, 17913304, 7684743, 1352767,
      25080576, 3186956, 22002790, 2048, 593920, 4272128, 3641344, 122880,
      921600, 21104640, 4395008, 4456448, 5595136, 4128768, 4587520, 30848472],
    #[18953784, 22595576, 4804850, 20954362, 20461191, 2957451, 4863257, 18375948,
      22102270, 20734015, 7347096, 2048, 593920, 7462912, 3641344, 122880,
      3022848, 22345728, 7720960, 6479872, 4427776, 987136, 7786496, 14291083],
    #[769255, 23316068, 1781904, 17589602, 3797834, 8335280, 19661107, 5879026,
      1610640, 24671970, 4599931, 2048, 4329472, 4345856, 1855488, 4009984,
      323584, 21268480, 4616192, 3203072, 2830336, 593920, 290816, 16367536],
    #[20703919, 17075991, 1796735, 20512029, 2028234, 7731112, 19727854, 5732206,
      7541367, 5639258, 4324398, 2048, 4390912, 5582848, 7180288, 7950336,
      3874816, 19802112, 6160384, 4997120, 188416, 4329472, 1183744, 10946472],
    #[276817, 2562490, 17078753, 2219651, 3303321, 7102518, 20461347, 22525806,
      7099881, 21580740, 6164400, 2048, 4575232, 5496832, 4943872, 6926336,
      4009984, 17700864, 6209536, 6987776, 323584, 6615040, 2363392, 9990198],
    #[18988213, 22091743, 20881504, 845202, 16904867, 21347090, 2823288, 24753394,
      17241906, 23589440, 6529163, 2048, 6750208, 6766592, 3981312, 1597440,
      122880, 21039104, 6713344, 1077248, 3022848, 2719744, 110592, 31701778],
    #[322168, 21243154, 18780256, 19466079, 17359197, 22252306, 868472, 24557324,
      18343762, 5517549, 24053208, 2048, 6799360, 4698112, 704512, 1597440,
      122880, 22145024, 7770112, 20480, 921600, 1675264, 1150976, 31828754],
    #[22824593, 21397603, 22315170, 4229601, 2336181, 7505209, 5175193, 5571934,
      6374894, 17739876, 5622305, 2048, 6926336, 1359872, 2555904, 3780608,
      2699264, 19159040, 1519616, 7528448, 4259840, 1740800, 6193152, 9811257],
    #[6051569, 7106864, 25015100, 4819583, 2937419, 25031367, 4489930, 21030899,
      5412643, 19805284, 5622305, 2048, 7950336, 2277376, 2555904, 3780608,
      1646592, 20080640, 462848, 4464640, 5365760, 2920448, 8286208, 28979911],
    #[17961881, 4778269, 24568345, 890150, 19156283, 8333172, 2669449, 3367067,
      4995364, 8193811, 24053208, 2048, 2834432, 3981312, 704512, 1597440,
      4096000, 23492608, 331776, 4464640, 4362240, 6479872, 6451200, 12248948],
    #[4855686, 24123329, 2678469, 22681553, 6828060, 3394603, 2124982, 18984064,
      973601, 7680053, 16835649, 2048, 5828608, 4943872, 3145728, 6926336,
      6176768, 22988800, 397312, 4464640, 6959104, 3203072, 1490944, 16059435],
    #[4627643, 22661764, 8022916, 23660980, 16838704, 4485920, 17155490, 20838065,
      5338580, 827360, 16976835, 2048, 32768, 5963776, 3174400, 6799360,
      3051520, 17278976, 4460544, 4464640, 847872, 4997120, 4501504, 12628768],
    #[24914312, 23768137, 22232186, 23424231, 18927696, 21868734, 16779023, 19732145,
      24977543, 20290590, 16779534, 2048, 2142208, 7192576, 24576, 6750208,
      958464, 18319360, 5431296, 7528448, 2805760, 6987776, 6443008, 32460990],
    #[7882445, 7177944, 3705541, 4691512, 6791358, 18226395, 17316191, 17104000,
      1497800, 24780903, 504074, 2048, 6123520, 7254016, 3198976, 4829184,
      6012928, 22779904, 2510848, 6414336, 6987776, 1077248, 3559424, 30428379]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters03Part00 : Array GeneratedNinthLowerSpinLetter := #[
  (5, false), (12, false), (12, false), (13, false),
  (12, false), (12, false), (13, false), (12, true),
  (13, false), (12, true), (13, false), (12, false),
  (12, false), (12, false), (13, false), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters03Part00.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_000 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 0 24 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_000 :
    generatedNinthLowerSpinSourceQReplayWord 3 0 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 0)
    0 24 0 (prefix_sizes 0) slice_000
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (0 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_001 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 24 48 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_001 :
    generatedNinthLowerSpinSourceQReplayWord 3 1 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 1)
    24 24 0 (prefix_sizes 1) slice_001
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (24 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_002 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 48 72 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_002 :
    generatedNinthLowerSpinSourceQReplayWord 3 2 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 2)
    48 24 0 (prefix_sizes 2) slice_002
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (48 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_003 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 72 96 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_003 :
    generatedNinthLowerSpinSourceQReplayWord 3 3 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 3)
    72 24 0 (prefix_sizes 3) slice_003
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (72 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_004 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 96 120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_004 :
    generatedNinthLowerSpinSourceQReplayWord 3 4 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 4)
    96 24 0 (prefix_sizes 4) slice_004
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (96 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_005 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 120 144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_005 :
    generatedNinthLowerSpinSourceQReplayWord 3 5 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 5)
    120 24 0 (prefix_sizes 5) slice_005
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_006 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 144 168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_006 :
    generatedNinthLowerSpinSourceQReplayWord 3 6 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 6)
    144 24 0 (prefix_sizes 6) slice_006
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_007 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 168 192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_007 :
    generatedNinthLowerSpinSourceQReplayWord 3 7 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 7)
    168 24 0 (prefix_sizes 7) slice_007
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_008 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 192 216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_008 :
    generatedNinthLowerSpinSourceQReplayWord 3 8 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 8)
    192 24 0 (prefix_sizes 8) slice_008
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_009 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 216 240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_009 :
    generatedNinthLowerSpinSourceQReplayWord 3 9 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 9)
    216 24 0 (prefix_sizes 9) slice_009
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_010 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 240 264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_010 :
    generatedNinthLowerSpinSourceQReplayWord 3 10 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 10)
    240 24 0 (prefix_sizes 10) slice_010
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_011 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 264 288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_011 :
    generatedNinthLowerSpinSourceQReplayWord 3 11 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 11)
    264 24 0 (prefix_sizes 11) slice_011
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_012 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 288 312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_012 :
    generatedNinthLowerSpinSourceQReplayWord 3 12 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 12)
    288 24 0 (prefix_sizes 12) slice_012
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_013 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 312 336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_013 :
    generatedNinthLowerSpinSourceQReplayWord 3 13 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 13)
    312 24 0 (prefix_sizes 13) slice_013
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_014 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 336 360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_014 :
    generatedNinthLowerSpinSourceQReplayWord 3 14 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 14)
    336 24 0 (prefix_sizes 14) slice_014
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_015 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 360 384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_015 :
    generatedNinthLowerSpinSourceQReplayWord 3 15 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 15)
    360 24 0 (prefix_sizes 15) slice_015
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_016 :
    generatedNinthLowerSpinSourceQReplayPrefixWords03.extract 384 408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_03_part_00_016 :
    generatedNinthLowerSpinSourceQReplayWord 3 16 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords03
    (generatedNinthLowerSpinLiteralQReplayPrefixes03Part00 16)
    384 24 0 (prefix_sizes 16) slice_016
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords03.getD (384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords03.extract 0 16 =
      generatedNinthLowerSpinLiteralQReplayLetters03Part00 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_03_part_00 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 3 ⟨0 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters03Part00.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords03
    generatedNinthLowerSpinLiteralQReplayLetters03Part00
    0 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords03.getD (0 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
