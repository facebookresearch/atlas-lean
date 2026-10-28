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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 : Fin 17 → Array ℕ :=
  ![
    #[28997282, 29503841, 409755, 11135211, 8199935, 27549105, 5030896, 25356996,
      19218590, 3298572, 3378304, 6094848, 6031365, 4766516, 21971062, 19120948,
      20290353, 20484921, 7735304, 5434172, 19279987, 8081413, 23744520, 29023213],
    #[10124474, 30307497, 17762291, 16610154, 804875, 31003788, 23253084, 14048068,
      3690748, 20335702, 24453275, 4485120, 24612623, 4510224, 4712343, 20949520,
      25023775, 21894687, 20906752, 432400, 876696, 17614607, 563968, 25835624],
    #[27638409, 14885555, 19019791, 13228704, 17305345, 11385243, 4497854, 8752777,
      1847632, 19343330, 7800819, 3588096, 22282591, 2405683, 18137773, 18005299,
      19090540, 16862304, 655372, 5606719, 16980978, 18889055, 18626572, 9778082],
    #[27978702, 15587804, 23377153, 29929958, 21377361, 30140151, 18130399, 26197916,
      16837050, 4475195, 2947087, 2473984, 6616251, 20197707, 2373097, 3275083,
      20815344, 18431216, 2556160, 22923339, 19450194, 2100411, 19351808, 25313772],
    #[11332526, 13101199, 23832223, 13305643, 7279279, 32805225, 3429855, 28339298,
      216855, 4521275, 18884956, 3403776, 22565256, 18117963, 2855543, 2604363,
      17276099, 18431216, 2818099, 4283768, 1772543, 18512264, 17528883, 10006751],
    #[16208744, 30469820, 21150326, 33010472, 7767193, 11045916, 20398526, 32740625,
      20226361, 21164060, 7551996, 86016, 19100495, 3310285, 1152810, 25164493,
      7731586, 16862304, 2606562, 23994159, 21904485, 19684175, 24976866, 28337740],
    #[30788581, 29566116, 1081559, 26671141, 19617904, 26603470, 2326620, 31157055,
      1338604, 3158064, 3219606, 5775360, 19350587, 261750, 6167765, 18085494,
      2318925, 21894687, 705618, 18969124, 24256750, 23231547, 21658706, 26599226],
    #[26617431, 11464092, 17849408, 12489936, 24183505, 9637239, 22803440, 12715754,
      17984592, 6666513, 21258365, 3182592, 2816016, 550697, 17739952, 20504361,
      1607481, 20484921, 54272, 17976105, 3166368, 2146320, 19586048, 8452069],
    #[10453417, 11668655, 16804896, 11445424, 24580817, 26454295, 4325390, 33059801,
      18115632, 22723215, 21476048, 1089536, 3983376, 20107802, 17735888, 3308058,
      16908810, 3290634, 3195904, 2031130, 2121920, 2146320, 17628160, 25854646],
    #[31465445, 15462845, 2080885, 26851463, 19810416, 27650878, 17371150, 29964916,
      1797198, 19931328, 18638207, 6135808, 19334203, 3256125, 5508215, 18970429,
      1356550, 24942420, 660562, 18277231, 24993868, 23231547, 21687378, 26037971],
    #[14334646, 13902403, 18527960, 10690004, 19810416, 10742622, 398320, 30035129,
      151504, 17825952, 19703071, 7036928, 19751176, 19635726, 24664356, 1799694,
      19056390, 23445706, 3393484, 18031042, 8085548, 22993160, 22269900, 9596205],
    #[12196440, 12850999, 5499977, 25902913, 24580817, 12665078, 20216726, 16325201,
      21200457, 16819054, 22096689, 5558272, 17811968, 19433460, 19114785, 6606836,
      19113460, 20968333, 18101881, 19442061, 7506209, 22524416, 6024825, 26179886],
    #[26266360, 32613144, 23161295, 8567755, 23907910, 13121948, 18100341, 25358089,
      20398539, 20152807, 23394020, 503808, 24752132, 20616548, 17737172, 2604388,
      7806304, 6499770, 21835994, 16780734, 20155856, 22022148, 3422426, 29749795],
    #[25402421, 13501670, 6781391, 9563398, 5663509, 16001199, 1529560, 9325146,
      16856523, 210311, 6393897, 2588672, 24757252, 1048663, 131207, 18552919,
      23854163, 4614935, 22308676, 18038547, 629891, 20995076, 2993988, 16392669],
    #[32366622, 31968594, 24518000, 32343536, 3270089, 29062301, 19586121, 12683766,
      785282, 17300290, 1126352, 2355200, 23228146, 3118351, 17489072, 24022287,
      185341, 3229383, 24302906, 20039733, 17693250, 20526834, 8371514, 15353166],
    #[11936574, 32840716, 18715939, 32253036, 20678796, 29520252, 2042319, 16249232,
      6011465, 3555526, 23383625, 3268608, 5875562, 6293505, 19976096, 23134209,
      3377003, 1171594, 3819489, 24684512, 20545738, 7417706, 23744481, 30811196],
    #[14553367, 16149758, 21336352, 31333663, 24228431, 29358557, 18636144, 9480819,
      20198965, 18571405, 22581707, 868352, 23998229, 993277, 25154712, 21901309,
      2961640, 24420429, 2494629, 22466392, 17982349, 21747477, 22657189, 31550959]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part17 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (12, true), (12, true), (13, true),
  (12, false), (12, false), (12, false), (13, true),
  (12, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part17.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_272 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6528 6552 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_272 :
    generatedNinthLowerSpinSourceQReplayWord 7 272 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 0)
    6528 24 0 (prefix_sizes 0) slice_272
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6528 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_273 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6552 6576 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_273 :
    generatedNinthLowerSpinSourceQReplayWord 7 273 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 1)
    6552 24 0 (prefix_sizes 1) slice_273
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6552 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_274 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6576 6600 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_274 :
    generatedNinthLowerSpinSourceQReplayWord 7 274 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 2)
    6576 24 0 (prefix_sizes 2) slice_274
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6576 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_275 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6600 6624 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_275 :
    generatedNinthLowerSpinSourceQReplayWord 7 275 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 3)
    6600 24 0 (prefix_sizes 3) slice_275
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6600 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_276 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6624 6648 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_276 :
    generatedNinthLowerSpinSourceQReplayWord 7 276 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 4)
    6624 24 0 (prefix_sizes 4) slice_276
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6624 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_277 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6648 6672 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_277 :
    generatedNinthLowerSpinSourceQReplayWord 7 277 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 5)
    6648 24 0 (prefix_sizes 5) slice_277
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6648 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_278 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6672 6696 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_278 :
    generatedNinthLowerSpinSourceQReplayWord 7 278 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 6)
    6672 24 0 (prefix_sizes 6) slice_278
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6672 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_279 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6696 6720 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_279 :
    generatedNinthLowerSpinSourceQReplayWord 7 279 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 7)
    6696 24 0 (prefix_sizes 7) slice_279
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6696 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_280 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6720 6744 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_280 :
    generatedNinthLowerSpinSourceQReplayWord 7 280 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 8)
    6720 24 0 (prefix_sizes 8) slice_280
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6720 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_281 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6744 6768 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_281 :
    generatedNinthLowerSpinSourceQReplayWord 7 281 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 9)
    6744 24 0 (prefix_sizes 9) slice_281
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6744 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_282 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6768 6792 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_282 :
    generatedNinthLowerSpinSourceQReplayWord 7 282 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 10)
    6768 24 0 (prefix_sizes 10) slice_282
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6768 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_283 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6792 6816 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_283 :
    generatedNinthLowerSpinSourceQReplayWord 7 283 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 11)
    6792 24 0 (prefix_sizes 11) slice_283
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6792 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_284 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6816 6840 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_284 :
    generatedNinthLowerSpinSourceQReplayWord 7 284 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 12)
    6816 24 0 (prefix_sizes 12) slice_284
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6816 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_285 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6840 6864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_285 :
    generatedNinthLowerSpinSourceQReplayWord 7 285 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 13)
    6840 24 0 (prefix_sizes 13) slice_285
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_286 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6864 6888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_286 :
    generatedNinthLowerSpinSourceQReplayWord 7 286 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 14)
    6864 24 0 (prefix_sizes 14) slice_286
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_287 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6888 6912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_287 :
    generatedNinthLowerSpinSourceQReplayWord 7 287 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 15)
    6888 24 0 (prefix_sizes 15) slice_287
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_288 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 6912 6936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_17_288 :
    generatedNinthLowerSpinSourceQReplayWord 7 288 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part17 16)
    6912 24 0 (prefix_sizes 16) slice_288
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (6912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 272 288 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part17 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_17 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨272 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part17.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part17
    272 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (272 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
