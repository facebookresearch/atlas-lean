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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 : Fin 17 → Array ℕ :=
  ![
    #[12699260, 32332160, 1220481, 32998324, 7149834, 9558595, 655806, 32579965,
      23491207, 20085274, 5785478, 17946624, 21683462, 23286926, 25130762, 24544398,
      1364360, 21746474, 1585826, 331308, 3258892, 18900230, 8352418, 11915686],
    #[25796803, 27192781, 22769048, 27866841, 18467594, 8790412, 17790431, 32074130,
      23606208, 2193213, 24023961, 19298304, 19971672, 22562965, 52816, 20064405,
      22662861, 7984677, 7088360, 17135741, 7761928, 19584600, 6121704, 32531172],
    #[25407984, 25681459, 6412459, 12563161, 3755786, 12251327, 2725343, 33180511,
      4706398, 18576910, 24430282, 20338688, 3397877, 8244792, 20172029, 3231288,
      8335053, 24072741, 8039656, 19290832, 7783432, 4161781, 4975848, 30614569],
    #[27792274, 11317784, 2227601, 27640906, 4468468, 29130669, 20836798, 31006475,
      24449278, 23384052, 932983, 23222272, 6114671, 21181671, 17649821, 23139559,
      19079560, 18453716, 4879708, 305595, 5533170, 25967, 2962780, 33052718],
    #[31822201, 12480824, 6023792, 31001916, 22777192, 9562213, 4821084, 32370953,
      4813712, 19381604, 20062416, 22411264, 3512800, 5358255, 21309058, 1127087,
      21496655, 2254669, 19530754, 16973485, 6467426, 786912, 24765442, 32727599],
    #[31866668, 13914897, 19647189, 27563491, 22985759, 8685328, 18101232, 26859005,
      3244663, 1703711, 23509439, 17139712, 1083554, 3269785, 23311803, 906393,
      24937531, 5865675, 20911344, 24164457, 21994777, 4968610, 25068784, 32574934],
    #[16321714, 14172738, 757461, 9737603, 7638348, 11379950, 851982, 8451683,
      19404265, 20712882, 6334911, 18069504, 18832188, 20206132, 22221243, 18764340,
      23073032, 5449208, 20911344, 7720644, 24574599, 23257916, 25052400, 32680827],
    #[14680457, 28959875, 4488738, 13880734, 22841555, 10201143, 21168142, 15561209,
      7595826, 17459341, 3616976, 22394880, 18176272, 6521620, 8381136, 2306836,
      8045060, 17884678, 19530754, 17874710, 25017280, 17584400, 22668290, 12858260],
    #[16249794, 32113818, 3450995, 10671530, 5273718, 31694365, 4718606, 8515419,
      19592524, 3811526, 17378423, 18524160, 20643135, 558647, 2119039, 5396023,
      3171080, 24258132, 4879708, 568171, 18466880, 24282431, 6980956, 28637950],
    #[13104034, 12800868, 17344800, 26702599, 6279048, 32730749, 23589872, 28613014,
      1055, 19103576, 3377444, 17602560, 1707327, 74185, 435487, 5046729,
      4134134, 24596729, 21001231, 19787206, 19515424, 7505215, 23102479, 9370573],
    #[29988968, 10336485, 20980269, 8400375, 5186741, 29479382, 4627350, 9922673,
      8334141, 503050, 1223457, 23209984, 6732048, 20201330, 6220593, 24911730,
      5664354, 21194351, 22358029, 1040255, 22290977, 807184, 19318797, 26379898],
    #[31312877, 30367327, 1740504, 13883795, 19579217, 29897649, 1335413, 28736812,
      1258980, 17815280, 8377812, 17819648, 6163260, 6430249, 6158052, 6438441,
      535829, 4286952, 4547837, 1090260, 5389784, 6480700, 275709, 11279401],
    #[15805118, 15105441, 4180085, 29567475, 17117871, 13763202, 17245912, 26909823,
      635095, 20759613, 22249607, 18860032, 22091938, 21125673, 22581289, 22174249,
      17922699, 5102811, 21411408, 1246329, 22579339, 21745826, 17245776, 10468068],
    #[26030164, 26342241, 16819232, 28428129, 24470681, 27599429, 4226121, 29395676,
      18992192, 2269714, 1920176, 17414144, 20035680, 2908116, 23879632, 1896404,
      5427124, 4395198, 2195210, 4958430, 23283632, 19988576, 610058, 30153126],
    #[26819068, 27536916, 21769695, 15206890, 1402992, 10857781, 20314575, 12565179,
      21040190, 2517050, 2908064, 19404800, 17662433, 23357253, 4505161, 19990341,
      23318180, 17629264, 3456756, 8253873, 22302632, 23632353, 7626484, 30724448],
    #[9345170, 10788294, 1980862, 27001248, 4870865, 15384594, 2329968, 25966245,
      18294497, 23656467, 2966680, 17029120, 6496095, 154311, 147915, 2226887,
      2981272, 17105136, 16960872, 21393327, 17759892, 2807647, 20049256, 27347437],
    #[11619180, 11651947, 2964243, 28717299, 4870865, 30655468, 20560963, 10248869,
      1173121, 23214400, 725144, 20305920, 4205970, 912697, 3286475, 3702073,
      19339435, 20119792, 2660443, 24341858, 870489, 3749266, 4036699, 9984627]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part13 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, false), (12, false),
  (12, false), (13, true), (12, true), (12, true),
  (13, false), (12, false), (12, false), (13, false),
  (12, false), (12, false), (12, false), (13, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part13.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_208 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4992 5016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_208 :
    generatedNinthLowerSpinSourceQReplayWord 5 208 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 0)
    4992 24 0 (prefix_sizes 0) slice_208
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_209 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5016 5040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_209 :
    generatedNinthLowerSpinSourceQReplayWord 5 209 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 1)
    5016 24 0 (prefix_sizes 1) slice_209
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_210 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5040 5064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_210 :
    generatedNinthLowerSpinSourceQReplayWord 5 210 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 2)
    5040 24 0 (prefix_sizes 2) slice_210
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_211 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5064 5088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_211 :
    generatedNinthLowerSpinSourceQReplayWord 5 211 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 3)
    5064 24 0 (prefix_sizes 3) slice_211
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_212 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5088 5112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_212 :
    generatedNinthLowerSpinSourceQReplayWord 5 212 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 4)
    5088 24 0 (prefix_sizes 4) slice_212
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_213 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5112 5136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_213 :
    generatedNinthLowerSpinSourceQReplayWord 5 213 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 5)
    5112 24 0 (prefix_sizes 5) slice_213
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_214 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5136 5160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_214 :
    generatedNinthLowerSpinSourceQReplayWord 5 214 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 6)
    5136 24 0 (prefix_sizes 6) slice_214
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_215 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5160 5184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_215 :
    generatedNinthLowerSpinSourceQReplayWord 5 215 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 7)
    5160 24 0 (prefix_sizes 7) slice_215
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_216 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5184 5208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_216 :
    generatedNinthLowerSpinSourceQReplayWord 5 216 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 8)
    5184 24 0 (prefix_sizes 8) slice_216
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_217 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5208 5232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_217 :
    generatedNinthLowerSpinSourceQReplayWord 5 217 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 9)
    5208 24 0 (prefix_sizes 9) slice_217
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_218 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5232 5256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_218 :
    generatedNinthLowerSpinSourceQReplayWord 5 218 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 10)
    5232 24 0 (prefix_sizes 10) slice_218
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_219 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5256 5280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_219 :
    generatedNinthLowerSpinSourceQReplayWord 5 219 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 11)
    5256 24 0 (prefix_sizes 11) slice_219
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_220 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5280 5304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_220 :
    generatedNinthLowerSpinSourceQReplayWord 5 220 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 12)
    5280 24 0 (prefix_sizes 12) slice_220
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_221 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5304 5328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_221 :
    generatedNinthLowerSpinSourceQReplayWord 5 221 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 13)
    5304 24 0 (prefix_sizes 13) slice_221
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_222 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5328 5352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_222 :
    generatedNinthLowerSpinSourceQReplayWord 5 222 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 14)
    5328 24 0 (prefix_sizes 14) slice_222
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_223 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5352 5376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_223 :
    generatedNinthLowerSpinSourceQReplayWord 5 223 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 15)
    5352 24 0 (prefix_sizes 15) slice_223
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_224 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 5376 5400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_13_224 :
    generatedNinthLowerSpinSourceQReplayWord 5 224 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part13 16)
    5376 24 0 (prefix_sizes 16) slice_224
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (5376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 208 224 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_13 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨208 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part13.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part13
    208 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (208 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
