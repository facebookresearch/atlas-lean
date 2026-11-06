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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 : Fin 17 → Array ℕ :=
  ![
    #[13933140, 16030354, 39200, 13110001, 18636680, 30973835, 17966064, 28592224,
      18938911, 6084440, 4569380, 17602560, 20106559, 16859593, 19830047, 5073353,
      1553654, 22253817, 21763087, 18998726, 2699296, 5918015, 23913487, 28320315],
    #[29478137, 30317473, 20748403, 32389777, 17111158, 15546662, 725006, 28465248,
      658764, 21315782, 23063671, 18524160, 1195327, 20510263, 19420543, 6434359,
      2675464, 22083156, 7345500, 177003, 3735616, 22695231, 5301596, 10057157],
    #[13933140, 16030354, 39200, 13110001, 18636680, 30973835, 17966064, 28592224,
      18938911, 6084440, 4569380, 17602560, 20106559, 16859593, 19830047, 5073353,
      1553654, 22253817, 21763087, 18998726, 2699296, 5918015, 23913487, 28320315],
    #[25242104, 33016181, 557, 13409383, 23336117, 9648198, 60310, 29913569,
      17613629, 18138378, 7007009, 23209984, 22378768, 6373234, 18746161, 19470194,
      3190370, 20227695, 21243917, 4970367, 2558497, 4167952, 20432909, 29026282],
    #[13824414, 16557100, 18263768, 9757664, 2629969, 14782914, 4874357, 15335263,
      22179300, 2649840, 1738196, 17819648, 18053948, 18136617, 24041188, 1349161,
      3407125, 723432, 3462397, 1555156, 19686872, 3119932, 7701757, 31254106],
    #[13042515, 31102028, 19257461, 27127838, 115375, 29537135, 22669016, 15527314,
      21506263, 1801277, 19923079, 18860032, 694434, 272937, 5083177, 18096681,
      17599115, 93403, 18347600, 277625, 1441931, 17848482, 22439504, 15106825],
    #[30037003, 15111998, 3146784, 12997438, 5129369, 9416218, 4709449, 13751939,
      652352, 21854738, 3779760, 17414144, 2697312, 24272852, 5631952, 4384724,
      1335220, 2953406, 651018, 4010206, 4353968, 19503200, 2219786, 30244345],
    #[29950209, 29648617, 1465823, 16474391, 19409008, 12811720, 22411727, 9898566,
      123966, 23044154, 1617824, 19404800, 1511905, 6080325, 22863433, 17411909,
      21102244, 17158224, 1990388, 7322033, 5683112, 24248801, 6209268, 25229725],
    #[15733407, 32772745, 16821727, 33228151, 19409008, 30001307, 5634511, 29056789,
      17758112, 7403428, 2599998, 18352128, 4121215, 5272182, 7125577, 18082422,
      21141513, 20168752, 903225, 22461007, 4796470, 24973951, 6146105, 26860035],
    #[13587707, 32916430, 17843232, 14047182, 5129369, 12009459, 21486665, 13227882,
      17380528, 22163120, 3783744, 17393664, 620688, 4574879, 5188482, 22361759,
      16977423, 2277404, 20053523, 20062348, 25029394, 19486864, 20749843, 30276873],
    #[30016259, 10297422, 1742965, 32527388, 115375, 8650767, 5891800, 29298418,
      6826119, 3025295, 20582615, 20305920, 4180210, 6850729, 19342795, 21479593,
      17274971, 16870715, 17413472, 2375113, 5174585, 19945714, 24147296, 12481369],
    #[16368046, 26485712, 3788504, 15750172, 2629969, 27844956, 21651573, 25419713,
      23223764, 1636847, 19301860, 17029120, 16784140, 25022052, 20013515, 5408356,
      916840, 19347771, 373843, 768567, 7832263, 2075404, 8172627, 10810986],
    #[13154788, 31890555, 24994349, 26737001, 23336117, 15136954, 16837526, 9101597,
      21902113, 4264046, 23210813, 19404800, 2152716, 22982648, 17063497, 7071736,
      24940276, 20235801, 4143341, 17385237, 17411909, 24996108, 7399661, 28588022],
    #[15116143, 28145610, 20154656, 26527657, 18636680, 10440411, 1188848, 12953904,
      23331108, 16842924, 17064991, 17414144, 4194308, 419598, 4485072, 24731406,
      23547658, 1460078, 21956708, 2150250, 4384724, 18788356, 19859556, 32829184],
    #[32736706, 10212266, 628851, 26768026, 17111158, 8784165, 17502222, 30369891,
      5129335, 2220236, 3712332, 20555776, 4224004, 17196814, 8240206, 6930190,
      4655882, 19289966, 25128036, 19946346, 7053386, 18744324, 20946020, 16596222],
    #[15116143, 28145610, 20154656, 26527657, 18636680, 10440411, 1188848, 12953904,
      23331108, 16842924, 17064991, 17414144, 4194308, 419598, 4485072, 24731406,
      23547658, 1460078, 21956708, 2150250, 4384724, 18788356, 19859556, 32829184],
    #[13154788, 31890555, 24994349, 26737001, 23336117, 15136954, 16837526, 9101597,
      21902113, 4264046, 23210813, 19404800, 2152716, 22982648, 17063497, 7071736,
      24940276, 20235801, 4143341, 17385237, 17411909, 24996108, 7399661, 28588022]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part15 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (13, false),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (13, true), (13, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part15.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_240 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5760 5784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_240 :
    generatedNinthLowerSpinSourceQReplayWord 5 240 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 0)
    5760 24 0 (prefix_sizes 0) slice_240
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_241 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5784 5808 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_241 :
    generatedNinthLowerSpinSourceQReplayWord 5 241 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 1)
    5784 24 0 (prefix_sizes 1) slice_241
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5784 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_242 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5808 5832 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_242 :
    generatedNinthLowerSpinSourceQReplayWord 5 242 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 2)
    5808 24 0 (prefix_sizes 2) slice_242
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5808 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_243 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5832 5856 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_243 :
    generatedNinthLowerSpinSourceQReplayWord 5 243 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 3)
    5832 24 0 (prefix_sizes 3) slice_243
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5832 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_244 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5856 5880 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_244 :
    generatedNinthLowerSpinSourceQReplayWord 5 244 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 4)
    5856 24 0 (prefix_sizes 4) slice_244
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5856 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_245 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5880 5904 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_245 :
    generatedNinthLowerSpinSourceQReplayWord 5 245 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 5)
    5880 24 0 (prefix_sizes 5) slice_245
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5880 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_246 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5904 5928 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_246 :
    generatedNinthLowerSpinSourceQReplayWord 5 246 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 6)
    5904 24 0 (prefix_sizes 6) slice_246
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5904 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_247 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5928 5952 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_247 :
    generatedNinthLowerSpinSourceQReplayWord 5 247 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 7)
    5928 24 0 (prefix_sizes 7) slice_247
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5928 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_248 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5952 5976 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_248 :
    generatedNinthLowerSpinSourceQReplayWord 5 248 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 8)
    5952 24 0 (prefix_sizes 8) slice_248
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5952 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_249 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5976 6000 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_249 :
    generatedNinthLowerSpinSourceQReplayWord 5 249 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 9)
    5976 24 0 (prefix_sizes 9) slice_249
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5976 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_250 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6000 6024 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_250 :
    generatedNinthLowerSpinSourceQReplayWord 5 250 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 10)
    6000 24 0 (prefix_sizes 10) slice_250
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6000 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_251 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6024 6048 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_251 :
    generatedNinthLowerSpinSourceQReplayWord 5 251 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 11)
    6024 24 0 (prefix_sizes 11) slice_251
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6024 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_252 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6048 6072 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_252 :
    generatedNinthLowerSpinSourceQReplayWord 5 252 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 12)
    6048 24 0 (prefix_sizes 12) slice_252
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6048 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_253 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6072 6096 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_253 :
    generatedNinthLowerSpinSourceQReplayWord 5 253 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 13)
    6072 24 0 (prefix_sizes 13) slice_253
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6072 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_254 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6096 6120 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_254 :
    generatedNinthLowerSpinSourceQReplayWord 5 254 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 14)
    6096 24 0 (prefix_sizes 14) slice_254
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6096 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_255 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6120 6144 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_255 :
    generatedNinthLowerSpinSourceQReplayWord 5 255 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 15)
    6120 24 0 (prefix_sizes 15) slice_255
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6120 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_256 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6144 6168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_15_256 :
    generatedNinthLowerSpinSourceQReplayWord 5 256 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part15 16)
    6144 24 0 (prefix_sizes 16) slice_256
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 240 256 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_15 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨240 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part15.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part15
    240 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (240 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
