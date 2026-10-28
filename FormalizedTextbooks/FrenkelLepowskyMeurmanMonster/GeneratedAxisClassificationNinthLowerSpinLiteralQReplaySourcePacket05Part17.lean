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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 : Fin 17 → Array ℕ :=
  ![
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
    #[28470899, 15647332, 4009506, 31452025, 8333523, 33408220, 4259854, 30067986,
      19343568, 2361743, 22640434, 18315264, 7999218, 6205432, 18918448, 19359736,
      23771402, 763417, 5934867, 18813163, 3869378, 18398962, 6733587, 28925038],
    #[29195757, 32355497, 19386225, 29736490, 7731680, 16499900, 22995952, 14680031,
      18294960, 3471855, 24729426, 19359744, 7348161, 6359046, 19962960, 18350086,
      8388551, 3871353, 24735166, 18179512, 19000209, 19165121, 22244798, 9858960],
    #[28267425, 29356385, 1270490, 9802969, 694434, 26109088, 3472278, 27521466,
      24549470, 21260113, 22801416, 23054336, 5882500, 22086146, 18259726, 6515202,
      24914054, 17303332, 6844322, 20737440, 1344906, 20214404, 6795170, 33041801],
    #[9479323, 10704400, 18753721, 11094960, 2697312, 27067536, 3997813, 15612240,
      1202430, 5394683, 17995250, 21407744, 20195399, 21891850, 1914872, 2650890,
      20020045, 17145051, 5662614, 17919132, 19441599, 1828935, 7301014, 25576268],
    #[25883080, 28730589, 1805940, 25585710, 1652832, 27985040, 17725144, 12769283,
      17525504, 5166504, 17262399, 21391360, 2669940, 6184714, 3432454, 19449610,
      17529470, 17426920, 24568726, 1158300, 869746, 19352948, 22012822, 25792722],
    #[11862159, 32989884, 22991911, 25633327, 2650593, 30944641, 1334345, 28521715,
      5992456, 22535824, 21412116, 22091776, 2161711, 978676, 24291842, 18654964,
      7494363, 23143086, 25036917, 165505, 380461, 22404143, 17004661, 32643761],
    #[30455484, 14687066, 3258400, 30432726, 18480991, 31017280, 21064143, 29472915,
      3439116, 19676549, 3211824, 20035584, 1387052, 19176808, 23511818, 71016,
      18624324, 4021092, 3257376, 20728136, 2122022, 18905644, 1164320, 29622183],
    #[31067300, 30456314, 3310113, 26246223, 968949, 27560908, 3329392, 9293452,
      22205188, 3219532, 19407125, 18114560, 19716389, 19450911, 1339658, 537631,
      19397946, 1704165, 3296735, 147904, 19673135, 821541, 6856159, 28205415],
    #[30169284, 12840759, 1208865, 26914172, 18587224, 9271378, 17353795, 25697345,
      23831802, 17940524, 1132171, 17987584, 18071259, 146764, 18991047, 19055948,
      17066903, 1664584, 18005471, 20467859, 49436, 261851, 22978015, 10011911],
    #[32234371, 25725720, 21958104, 33326627, 21441798, 13687806, 8134861, 29619139,
      20241762, 22567201, 1974346, 23701504, 23988410, 20983602, 565382, 3393330,
      23834504, 17303094, 47550, 8144524, 19972156, 4753594, 4757950, 10699277],
    #[29899054, 10996966, 6527115, 12801501, 7637963, 32517118, 23056896, 31457550,
      2174895, 5327583, 1148884, 21583872, 21061412, 22028114, 513912, 333650,
      4339830, 19157861, 1280787, 24728641, 92, 5754660, 7043859, 10703469],
    #[26661411, 31069522, 1189808, 13492912, 22609016, 32764824, 17369092, 15781890,
      3324779, 20854344, 23138117, 18561024, 18785499, 16782344, 17010475, 7781384,
      24709331, 19351320, 22290379, 22313923, 19923952, 4404443, 22306763, 30252312]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part17 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false),
  (13, false), (12, false), (13, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part17.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_272 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6528 6552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_272 :
    generatedNinthLowerSpinSourceQReplayWord 5 272 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 0)
    6528 24 0 (prefix_sizes 0) slice_272
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_273 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6552 6576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_273 :
    generatedNinthLowerSpinSourceQReplayWord 5 273 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 1)
    6552 24 0 (prefix_sizes 1) slice_273
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_274 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6576 6600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_274 :
    generatedNinthLowerSpinSourceQReplayWord 5 274 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 2)
    6576 24 0 (prefix_sizes 2) slice_274
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_275 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6600 6624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_275 :
    generatedNinthLowerSpinSourceQReplayWord 5 275 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 3)
    6600 24 0 (prefix_sizes 3) slice_275
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_276 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6624 6648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_276 :
    generatedNinthLowerSpinSourceQReplayWord 5 276 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 4)
    6624 24 0 (prefix_sizes 4) slice_276
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_277 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6648 6672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_277 :
    generatedNinthLowerSpinSourceQReplayWord 5 277 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 5)
    6648 24 0 (prefix_sizes 5) slice_277
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_278 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6672 6696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_278 :
    generatedNinthLowerSpinSourceQReplayWord 5 278 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 6)
    6672 24 0 (prefix_sizes 6) slice_278
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_279 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6696 6720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_279 :
    generatedNinthLowerSpinSourceQReplayWord 5 279 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 7)
    6696 24 0 (prefix_sizes 7) slice_279
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_280 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6720 6744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_280 :
    generatedNinthLowerSpinSourceQReplayWord 5 280 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 8)
    6720 24 0 (prefix_sizes 8) slice_280
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_281 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6744 6768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_281 :
    generatedNinthLowerSpinSourceQReplayWord 5 281 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 9)
    6744 24 0 (prefix_sizes 9) slice_281
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_282 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6768 6792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_282 :
    generatedNinthLowerSpinSourceQReplayWord 5 282 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 10)
    6768 24 0 (prefix_sizes 10) slice_282
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_283 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6792 6816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_283 :
    generatedNinthLowerSpinSourceQReplayWord 5 283 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 11)
    6792 24 0 (prefix_sizes 11) slice_283
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_284 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6816 6840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_284 :
    generatedNinthLowerSpinSourceQReplayWord 5 284 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 12)
    6816 24 0 (prefix_sizes 12) slice_284
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_285 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6840 6864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_285 :
    generatedNinthLowerSpinSourceQReplayWord 5 285 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 13)
    6840 24 0 (prefix_sizes 13) slice_285
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_286 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6864 6888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_286 :
    generatedNinthLowerSpinSourceQReplayWord 5 286 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 14)
    6864 24 0 (prefix_sizes 14) slice_286
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_287 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6888 6912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_287 :
    generatedNinthLowerSpinSourceQReplayWord 5 287 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 15)
    6888 24 0 (prefix_sizes 15) slice_287
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_288 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 6912 6936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_17_288 :
    generatedNinthLowerSpinSourceQReplayWord 5 288 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part17 16)
    6912 24 0 (prefix_sizes 16) slice_288
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (6912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 272 288 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part17 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_17 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨272 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part17.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part17
    272 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (272 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
