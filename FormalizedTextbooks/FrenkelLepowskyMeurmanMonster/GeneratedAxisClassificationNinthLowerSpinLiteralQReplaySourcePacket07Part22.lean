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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 : Fin 17 → Array ℕ :=
  ![
    #[15557277, 16393564, 7608170, 32897725, 21724322, 8674193, 17369092, 32860370,
      18004742, 22480530, 16920363, 23410688, 24220780, 21402811, 6924101, 4820155,
      5290199, 4968360, 22159231, 5272516, 3320617, 2864236, 4183935, 10075557],
    #[12172934, 29131778, 17760021, 8768679, 22794142, 29853066, 19054860, 28988081,
      4786698, 19674763, 609064, 17496064, 20016415, 180575, 20470471, 17553759,
      18048064, 1146516, 22348500, 19135371, 2154456, 195871, 2153172, 12081773],
    #[28239031, 30557424, 6595127, 10889583, 6815111, 11196351, 787212, 26662823,
      2980102, 24199242, 6447141, 24913920, 22778673, 8138511, 5455732, 20854543,
      18379838, 19784841, 5187767, 21516216, 3757125, 1033009, 17387703, 28517656],
    #[9753183, 31822944, 19637482, 15658526, 20915010, 9388123, 3439368, 26999143,
      16826894, 24677058, 17829072, 24664064, 17755876, 24643589, 7869483, 3866629,
      25140961, 24181568, 18488737, 4541860, 24421071, 2125540, 4461985, 15621838],
    #[11207073, 30626912, 3285780, 31600429, 17818402, 26543464, 19741942, 12283143,
      836413, 4492177, 18877616, 24680448, 19753001, 23961256, 7516440, 2639528,
      7970433, 25110750, 3534431, 7276791, 22778161, 1296425, 23799391, 12763037],
    #[25486565, 32998640, 5514807, 9153654, 5061925, 12388084, 1869580, 27480919,
      2161695, 24511985, 6856839, 22816768, 6509096, 21708468, 23182911, 2897588,
      1537180, 17638521, 23099621, 5594705, 3539991, 20075048, 393445, 9515171],
    #[31006518, 30815234, 8133447, 11127749, 1797758, 9725706, 18322782, 29734579,
      2276712, 21008393, 17717960, 21841920, 17120815, 20353935, 5498951, 8334223,
      3765664, 7786180, 21644132, 24578283, 24653416, 4804143, 7875428, 32287983],
    #[13212502, 14235644, 24071562, 28544758, 89933, 26395402, 17082355, 32130381,
      19454043, 22398628, 17644645, 24872960, 3861969, 20140322, 22003060, 4864290,
      357619, 7710825, 6493338, 21867960, 21727397, 24137169, 21449882, 13675964],
    #[13444028, 32150798, 861073, 28155396, 18750676, 31373826, 24442895, 33033692,
      22761407, 5703604, 5839871, 22296576, 7300142, 5395501, 19051471, 19749933,
      18167811, 388781, 8367790, 4305539, 19275745, 20489262, 17229486, 28694659],
    #[30670882, 32458691, 20046530, 8915145, 17733812, 30587697, 4782428, 29625487,
      22564210, 7884842, 4995410, 21153792, 22063024, 23168736, 17916162, 3038944,
      18426192, 18206381, 21196797, 21524765, 19717810, 3651504, 1759229, 10090960],
    #[30727200, 24084427, 3224257, 29922496, 5120185, 26369844, 17316191, 17104000,
      10000763, 7927845, 17623379, 16959500, 13675450, 14781159, 17936646, 32396005,
      5841245, 14017196, 25381878, 4741400, 32244402, 12039092, 26932210, 31061471],
    #[27149791, 22391686, 1371510, 32759153, 22742447, 10737643, 16779023, 19732145,
      11289634, 17405136, 4723727, 789248, 25872724, 29930837, 4962830, 13549147,
      16886785, 32893034, 29645204, 20590896, 30128980, 12587354, 11745432, 11026878],
    #[9999839, 5443462, 2202555, 15527663, 5965231, 9478470, 17155490, 20838065,
      8763324, 17401008, 22164828, 17111294, 25197575, 30487211, 23157565, 31926693,
      2383532, 31244180, 13515943, 1048675, 13823178, 12810231, 9792664, 26952467],
    #[15846432, 22051737, 19510232, 13435952, 21897401, 8773263, 2124982, 18984064,
      12110219, 7530631, 17513704, 854110, 31996499, 30478055, 20751391, 31327973,
      7664820, 29734572, 26331837, 5201059, 32937488, 27320847, 8419232, 30695478],
    #[28180597, 7311089, 2598779, 25756750, 1968858, 9278610, 2669449, 3367067,
      28613324, 20763336, 6023993, 4786352, 10755511, 10235696, 18163048, 29111870,
      1127047, 32554164, 25567698, 1048765, 10457441, 27264009, 11535536, 10599186],
    #[30497686, 5953541, 21913542, 25876697, 22939505, 29091246, 4489930, 21030899,
      9666628, 23028292, 7437855, 21681365, 30486402, 8887362, 6289140, 13471048,
      1311680, 26151559, 12944509, 21659866, 10146985, 27218525, 26151047, 26453305],
    #[15851414, 4808360, 5176230, 11099668, 4466210, 26146563, 5175193, 5571934,
      11863076, 23860457, 7896449, 6902296, 30486402, 11042780, 23892025, 15140891,
      19730526, 9870617, 12998352, 7595844, 28922468, 11096669, 9805268, 29106887]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part22 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, false), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true),
  (13, true), (14, false), (12, false), (13, true),
  (12, true), (12, true), (12, true), (13, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part22.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_352 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8448 8472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_352 :
    generatedNinthLowerSpinSourceQReplayWord 7 352 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 0)
    8448 24 0 (prefix_sizes 0) slice_352
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_353 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8472 8496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_353 :
    generatedNinthLowerSpinSourceQReplayWord 7 353 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 1)
    8472 24 0 (prefix_sizes 1) slice_353
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_354 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8496 8520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_354 :
    generatedNinthLowerSpinSourceQReplayWord 7 354 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 2)
    8496 24 0 (prefix_sizes 2) slice_354
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_355 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8520 8544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_355 :
    generatedNinthLowerSpinSourceQReplayWord 7 355 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 3)
    8520 24 0 (prefix_sizes 3) slice_355
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_356 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8544 8568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_356 :
    generatedNinthLowerSpinSourceQReplayWord 7 356 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 4)
    8544 24 0 (prefix_sizes 4) slice_356
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_357 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8568 8592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_357 :
    generatedNinthLowerSpinSourceQReplayWord 7 357 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 5)
    8568 24 0 (prefix_sizes 5) slice_357
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_358 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8592 8616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_358 :
    generatedNinthLowerSpinSourceQReplayWord 7 358 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 6)
    8592 24 0 (prefix_sizes 6) slice_358
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_359 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8616 8640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_359 :
    generatedNinthLowerSpinSourceQReplayWord 7 359 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 7)
    8616 24 0 (prefix_sizes 7) slice_359
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_360 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8640 8664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_360 :
    generatedNinthLowerSpinSourceQReplayWord 7 360 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 8)
    8640 24 0 (prefix_sizes 8) slice_360
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_361 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8664 8688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_361 :
    generatedNinthLowerSpinSourceQReplayWord 7 361 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 9)
    8664 24 0 (prefix_sizes 9) slice_361
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_362 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8688 8712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_362 :
    generatedNinthLowerSpinSourceQReplayWord 7 362 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 10)
    8688 24 0 (prefix_sizes 10) slice_362
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_363 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8712 8736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_363 :
    generatedNinthLowerSpinSourceQReplayWord 7 363 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 11)
    8712 24 0 (prefix_sizes 11) slice_363
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_364 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8736 8760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_364 :
    generatedNinthLowerSpinSourceQReplayWord 7 364 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 12)
    8736 24 0 (prefix_sizes 12) slice_364
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_365 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8760 8784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_365 :
    generatedNinthLowerSpinSourceQReplayWord 7 365 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 13)
    8760 24 0 (prefix_sizes 13) slice_365
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_366 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8784 8808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_366 :
    generatedNinthLowerSpinSourceQReplayWord 7 366 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 14)
    8784 24 0 (prefix_sizes 14) slice_366
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_367 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8808 8832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_367 :
    generatedNinthLowerSpinSourceQReplayWord 7 367 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 15)
    8808 24 0 (prefix_sizes 15) slice_367
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_368 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 8832 8856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_22_368 :
    generatedNinthLowerSpinSourceQReplayWord 7 368 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part22 16)
    8832 24 0 (prefix_sizes 16) slice_368
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (8832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 352 368 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part22 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_22 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨352 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part22.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part22
    352 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (352 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
