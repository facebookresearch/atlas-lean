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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 : Fin 17 → Array ℕ :=
  ![
    #[13154788, 31890555, 24994349, 26737001, 23336117, 15136954, 16837526, 9101597,
      21902113, 4264046, 23210813, 19404800, 2152716, 22982648, 17063497, 7071736,
      24940276, 20235801, 4143341, 17385237, 17411909, 24996108, 7399661, 28588022],
    #[16368046, 26485712, 3788504, 15750172, 2629969, 27844956, 21651573, 25419713,
      23223764, 1636847, 19301860, 17029120, 16784140, 25022052, 20013515, 5408356,
      916840, 19347771, 373843, 768567, 7832263, 2075404, 8172627, 10810986],
    #[30016259, 10297422, 1742965, 32527388, 115375, 8650767, 5891800, 29298418,
      6826119, 3025295, 20582615, 20305920, 4180210, 6850729, 19342795, 21479593,
      17274971, 16870715, 17413472, 2375113, 5174585, 19945714, 24147296, 12481369],
    #[13587707, 32916430, 17843232, 14047182, 5129369, 12009459, 21486665, 13227882,
      17380528, 22163120, 3783744, 17393664, 620688, 4574879, 5188482, 22361759,
      16977423, 2277404, 20053523, 20062348, 25029394, 19486864, 20749843, 30276873],
    #[15733407, 32772745, 16821727, 33228151, 19409008, 30001307, 5634511, 29056789,
      17758112, 7403428, 2599998, 18352128, 4121215, 5272182, 7125577, 18082422,
      21141513, 20168752, 903225, 22461007, 4796470, 24973951, 6146105, 26860035],
    #[31853960, 13554874, 3938750, 12024028, 23663313, 8656000, 23879024, 8913463,
      21269656, 1254804, 7993057, 20756480, 3013926, 18626775, 17712693, 3604695,
      24448497, 22321425, 20763872, 7269431, 525075, 22269222, 21198048, 29502711],
    #[15382715, 15835940, 2702099, 25671868, 24052433, 8520832, 4635715, 10589641,
      24262808, 19501223, 25163393, 17479680, 18389899, 16821732, 3682869, 898532,
      8003183, 22776463, 18543840, 4503812, 17629630, 6712203, 23434464, 30296484],
    #[28978849, 31648549, 17727435, 15719262, 23031366, 11202225, 19800269, 32438412,
      4618355, 21288593, 1849672, 23730176, 23281592, 17487440, 17184740, 52816,
      23462376, 931512, 21186384, 852224, 704604, 2654136, 24061776, 16704110],
    #[26926753, 15621654, 18561286, 30358334, 6544149, 12193457, 721408, 15661196,
      23890208, 6616817, 3570715, 21821440, 8038438, 20956413, 3772442, 3394813,
      22717659, 19750933, 22717646, 1519667, 17563708, 20396070, 23131342, 15868765],
    #[8448873, 9342664, 7176718, 31680791, 7177673, 26163289, 964612, 14864975,
      17089069, 21259161, 20023857, 24655872, 23287843, 21584029, 756274, 872605,
      19118270, 4257217, 20155775, 2069986, 23980561, 1009699, 18210175, 28312581],
    #[26926753, 15621654, 18561286, 30358334, 6544149, 12193457, 721408, 15661196,
      23890208, 6616817, 3570715, 21821440, 8038438, 20956413, 3772442, 3394813,
      22717659, 19750933, 22717646, 1519667, 17563708, 20396070, 23131342, 15868765],
    #[28978849, 31648549, 17727435, 15719262, 23031366, 11202225, 19800269, 32438412,
      4618355, 21288593, 1849672, 23730176, 23281592, 17487440, 17184740, 52816,
      23462376, 931512, 21186384, 852224, 704604, 2654136, 24061776, 16704110],
    #[15382715, 15835940, 2702099, 25671868, 24052433, 8520832, 4635715, 10589641,
      24262808, 19501223, 25163393, 17479680, 18389899, 16821732, 3682869, 898532,
      8003183, 22776463, 18543840, 4503812, 17629630, 6712203, 23434464, 30296484],
    #[31853960, 13554874, 3938750, 12024028, 23663313, 8656000, 23879024, 8913463,
      21269656, 1254804, 7993057, 20756480, 3013926, 18626775, 17712693, 3604695,
      24448497, 22321425, 20763872, 7269431, 525075, 22269222, 21198048, 29502711],
    #[15733407, 32772745, 16821727, 33228151, 19409008, 30001307, 5634511, 29056789,
      17758112, 7403428, 2599998, 18352128, 4121215, 5272182, 7125577, 18082422,
      21141513, 20168752, 903225, 22461007, 4796470, 24973951, 6146105, 26860035],
    #[13587707, 32916430, 17843232, 14047182, 5129369, 12009459, 21486665, 13227882,
      17380528, 22163120, 3783744, 17393664, 620688, 4574879, 5188482, 22361759,
      16977423, 2277404, 20053523, 20062348, 25029394, 19486864, 20749843, 30276873],
    #[30016259, 10297422, 1742965, 32527388, 115375, 8650767, 5891800, 29298418,
      6826119, 3025295, 20582615, 20305920, 4180210, 6850729, 19342795, 21479593,
      17274971, 16870715, 17413472, 2375113, 5174585, 19945714, 24147296, 12481369]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part16 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, true), (13, true), (12, true),
  (13, true), (12, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part16.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_256 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6144 6168 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_256 :
    generatedNinthLowerSpinSourceQReplayWord 5 256 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 0)
    6144 24 0 (prefix_sizes 0) slice_256
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6144 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_257 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6168 6192 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_257 :
    generatedNinthLowerSpinSourceQReplayWord 5 257 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 1)
    6168 24 0 (prefix_sizes 1) slice_257
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6168 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_258 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6192 6216 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_258 :
    generatedNinthLowerSpinSourceQReplayWord 5 258 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 2)
    6192 24 0 (prefix_sizes 2) slice_258
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6192 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_259 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6216 6240 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_259 :
    generatedNinthLowerSpinSourceQReplayWord 5 259 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 3)
    6216 24 0 (prefix_sizes 3) slice_259
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6216 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_260 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6240 6264 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_260 :
    generatedNinthLowerSpinSourceQReplayWord 5 260 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 4)
    6240 24 0 (prefix_sizes 4) slice_260
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6240 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_261 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6264 6288 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_261 :
    generatedNinthLowerSpinSourceQReplayWord 5 261 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 5)
    6264 24 0 (prefix_sizes 5) slice_261
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6264 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_262 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6288 6312 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_262 :
    generatedNinthLowerSpinSourceQReplayWord 5 262 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 6)
    6288 24 0 (prefix_sizes 6) slice_262
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6288 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_263 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6312 6336 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_263 :
    generatedNinthLowerSpinSourceQReplayWord 5 263 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 7)
    6312 24 0 (prefix_sizes 7) slice_263
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6312 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_264 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6336 6360 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_264 :
    generatedNinthLowerSpinSourceQReplayWord 5 264 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 8)
    6336 24 0 (prefix_sizes 8) slice_264
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6336 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_265 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6360 6384 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_265 :
    generatedNinthLowerSpinSourceQReplayWord 5 265 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 9)
    6360 24 0 (prefix_sizes 9) slice_265
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6360 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_266 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6384 6408 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_266 :
    generatedNinthLowerSpinSourceQReplayWord 5 266 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 10)
    6384 24 0 (prefix_sizes 10) slice_266
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6384 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_267 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6408 6432 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_267 :
    generatedNinthLowerSpinSourceQReplayWord 5 267 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 11)
    6408 24 0 (prefix_sizes 11) slice_267
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6408 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_268 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6432 6456 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_268 :
    generatedNinthLowerSpinSourceQReplayWord 5 268 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 12)
    6432 24 0 (prefix_sizes 12) slice_268
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6432 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_269 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6456 6480 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_269 :
    generatedNinthLowerSpinSourceQReplayWord 5 269 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 13)
    6456 24 0 (prefix_sizes 13) slice_269
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6456 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_270 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6480 6504 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_270 :
    generatedNinthLowerSpinSourceQReplayWord 5 270 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 14)
    6480 24 0 (prefix_sizes 14) slice_270
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6480 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_271 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6504 6528 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_271 :
    generatedNinthLowerSpinSourceQReplayWord 5 271 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 15)
    6504 24 0 (prefix_sizes 15) slice_271
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6504 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_272 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6528 6552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_16_272 :
    generatedNinthLowerSpinSourceQReplayWord 5 272 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part16 16)
    6528 24 0 (prefix_sizes 16) slice_272
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 256 272 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_16 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨256 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part16.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part16
    256 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (256 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
