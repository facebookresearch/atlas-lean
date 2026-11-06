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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 : Fin 17 → Array ℕ :=
  ![
    #[11619180, 11651947, 2964243, 28717299, 4870865, 30655468, 20560963, 10248869,
      1173121, 23214400, 725144, 20305920, 4205970, 912697, 3286475, 3702073,
      19339435, 20119792, 2660443, 24341858, 870489, 3749266, 4036699, 9984627],
    #[11602665, 25632534, 21397451, 29917037, 5213766, 29498278, 5718221, 12713371,
      18610504, 20921292, 20390003, 17393664, 1427075, 25158418, 24550274, 23114514,
      18541969, 21128094, 380431, 21075229, 789761, 2670211, 3964431, 9238054],
    #[12041865, 12024598, 24365318, 30580286, 24328981, 13930438, 21148160, 29837819,
      17927195, 2148434, 2949408, 17393664, 2802973, 25158418, 24550274, 23114514,
      1392143, 5542814, 3804561, 6841987, 17030815, 3251485, 245137, 8815477],
    #[11078468, 16718138, 6124046, 29155045, 18941385, 26728315, 23705604, 32705901,
      4745777, 1039358, 2353709, 18352128, 25114687, 4864054, 24435273, 6662198,
      7669769, 7869049, 5667440, 3193414, 22770294, 18391103, 5118576, 26493992],
    #[26434388, 32231722, 22270478, 29155061, 17657289, 28145515, 7845892, 15797629,
      21377585, 18476030, 17152557, 18352128, 8372287, 8308790, 7125577, 22106166,
      21037065, 23102073, 24832624, 19454534, 21228150, 18370623, 23235184, 10636344],
    #[14793557, 30030123, 250382, 32497396, 7177673, 27033450, 3651588, 13766012,
      5585457, 7005182, 1356333, 18352128, 3983423, 25020470, 20757065, 22173750,
      67593, 3377785, 23718512, 20501062, 22080118, 5984319, 24218224, 31540281],
    #[14793589, 16754955, 17175054, 32669396, 7177673, 27037514, 17741828, 33211740,
      22020657, 21222398, 358957, 18352128, 3946559, 22100022, 2415177, 8298550,
      2951177, 2822777, 6126192, 2142790, 4749942, 22784063, 4528752, 30229529],
    #[25904026, 26183173, 551174, 32207661, 6544149, 29510357, 17498624, 29392104,
      2634779, 23646290, 3625248, 17393664, 23647517, 7635730, 8125314, 23845650,
      6049295, 6026142, 8134033, 2432643, 5023391, 7570717, 4566417, 11329126],
    #[12449690, 27902565, 1785803, 13074974, 23031366, 13819605, 3023053, 31521000,
      2244936, 6800332, 18575475, 17393664, 24196739, 6468370, 6151042, 25029394,
      23285137, 24974238, 4398607, 18488605, 21214465, 4998787, 8039951, 8817493],
    #[32632482, 12447397, 17939219, 32806205, 24052433, 9711138, 21412931, 28335979,
      17100417, 4813120, 3555480, 20305920, 23702930, 24866105, 21722571, 5174585,
      24647851, 17367280, 5085275, 23127394, 22909017, 1097106, 5806171, 26152893],
    #[33423345, 29203109, 20220350, 33248963, 23663313, 27193201, 7101808, 27593158,
      2363105, 6656019, 2495640, 17029120, 24809311, 22293191, 23851467, 7832263,
      6462872, 20517104, 24198504, 23324591, 8312468, 3362655, 21110120, 26558094],
    #[29950209, 29648617, 1465823, 16474391, 19409008, 12811720, 22411727, 9898566,
      123966, 23044154, 1617824, 19404800, 1511905, 6080325, 22863433, 17411909,
      21102244, 17158224, 1990388, 7322033, 5683112, 24248801, 6209268, 25229725],
    #[30037003, 15111998, 3146784, 12997438, 5129369, 9416218, 4709449, 13751939,
      652352, 21854738, 3779760, 17414144, 2697312, 24272852, 5631952, 4384724,
      1335220, 2953406, 651018, 4010206, 4353968, 19503200, 2219786, 30244345],
    #[13042515, 31102028, 19257461, 27127838, 115375, 29537135, 22669016, 15527314,
      21506263, 1801277, 19923079, 18860032, 694434, 272937, 5083177, 18096681,
      17599115, 93403, 18347600, 277625, 1441931, 17848482, 22439504, 15106825],
    #[13824414, 16557100, 18263768, 9757664, 2629969, 14782914, 4874357, 15335263,
      22179300, 2649840, 1738196, 17819648, 18053948, 18136617, 24041188, 1349161,
      3407125, 723432, 3462397, 1555156, 19686872, 3119932, 7701757, 31254106],
    #[25242104, 33016181, 557, 13409383, 23336117, 9648198, 60310, 29913569,
      17613629, 18138378, 7007009, 23209984, 22378768, 6373234, 18746161, 19470194,
      3190370, 20227695, 21243917, 4970367, 2558497, 4167952, 20432909, 29026282],
    #[13933140, 16030354, 39200, 13110001, 18636680, 30973835, 17966064, 28592224,
      18938911, 6084440, 4569380, 17602560, 20106559, 16859593, 19830047, 5073353,
      1553654, 22253817, 21763087, 18998726, 2699296, 5918015, 23913487, 28320315]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part14 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, false), (12, false), (4, true),
  (0, false), (5, false), (12, true), (13, true),
  (12, true), (13, true), (12, true), (12, true),
  (12, true), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part14.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_224 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5376 5400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_224 :
    generatedNinthLowerSpinSourceQReplayWord 5 224 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 0)
    5376 24 0 (prefix_sizes 0) slice_224
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_225 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5400 5424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_225 :
    generatedNinthLowerSpinSourceQReplayWord 5 225 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 1)
    5400 24 0 (prefix_sizes 1) slice_225
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_226 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5424 5448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_226 :
    generatedNinthLowerSpinSourceQReplayWord 5 226 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 2)
    5424 24 0 (prefix_sizes 2) slice_226
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_227 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5448 5472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_227 :
    generatedNinthLowerSpinSourceQReplayWord 5 227 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 3)
    5448 24 0 (prefix_sizes 3) slice_227
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_228 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5472 5496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_228 :
    generatedNinthLowerSpinSourceQReplayWord 5 228 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 4)
    5472 24 0 (prefix_sizes 4) slice_228
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_229 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5496 5520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_229 :
    generatedNinthLowerSpinSourceQReplayWord 5 229 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 5)
    5496 24 0 (prefix_sizes 5) slice_229
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_230 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5520 5544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_230 :
    generatedNinthLowerSpinSourceQReplayWord 5 230 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 6)
    5520 24 0 (prefix_sizes 6) slice_230
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_231 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5544 5568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_231 :
    generatedNinthLowerSpinSourceQReplayWord 5 231 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 7)
    5544 24 0 (prefix_sizes 7) slice_231
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_232 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5568 5592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_232 :
    generatedNinthLowerSpinSourceQReplayWord 5 232 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 8)
    5568 24 0 (prefix_sizes 8) slice_232
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_233 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5592 5616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_233 :
    generatedNinthLowerSpinSourceQReplayWord 5 233 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 9)
    5592 24 0 (prefix_sizes 9) slice_233
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_234 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5616 5640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_234 :
    generatedNinthLowerSpinSourceQReplayWord 5 234 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 10)
    5616 24 0 (prefix_sizes 10) slice_234
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_235 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5640 5664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_235 :
    generatedNinthLowerSpinSourceQReplayWord 5 235 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 11)
    5640 24 0 (prefix_sizes 11) slice_235
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_236 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5664 5688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_236 :
    generatedNinthLowerSpinSourceQReplayWord 5 236 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 12)
    5664 24 0 (prefix_sizes 12) slice_236
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_237 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5688 5712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_237 :
    generatedNinthLowerSpinSourceQReplayWord 5 237 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 13)
    5688 24 0 (prefix_sizes 13) slice_237
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_238 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5712 5736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_238 :
    generatedNinthLowerSpinSourceQReplayWord 5 238 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 14)
    5712 24 0 (prefix_sizes 14) slice_238
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_239 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5736 5760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_239 :
    generatedNinthLowerSpinSourceQReplayWord 5 239 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 15)
    5736 24 0 (prefix_sizes 15) slice_239
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_240 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5760 5784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_14_240 :
    generatedNinthLowerSpinSourceQReplayWord 5 240 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part14 16)
    5760 24 0 (prefix_sizes 16) slice_240
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 224 240 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_14 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨224 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part14.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part14
    224 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (224 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
