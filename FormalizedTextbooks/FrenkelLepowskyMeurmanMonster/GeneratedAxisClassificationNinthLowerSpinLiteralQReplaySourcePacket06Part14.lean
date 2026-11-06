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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 : Fin 17 → Array ℕ :=
  ![
    #[29574044, 32359730, 3980177, 14550590, 25156801, 10476071, 24442895, 32533994,
      22927279, 2660260, 21961724, 24918016, 1598526, 7427133, 23641027, 5133373,
      21051395, 1058481, 552626, 21721743, 7544829, 2599998, 24061618, 11237546],
    #[31092834, 30988191, 19950274, 13817709, 8048140, 9862617, 4782428, 13839143,
      6215010, 17236026, 24119298, 23775232, 1537952, 4495088, 7170318, 4949744,
      24897872, 448177, 311265, 24408337, 25153198, 1617824, 21170145, 9625396],
    #[14330984, 22556562, 24163014, 5439330, 28969484, 5694936, 17316191, 26455853,
      14551394, 17276976, 3201024, 19580940, 9925544, 29661945, 2980102, 30116599,
      3926353, 25572018, 29643748, 24418584, 12573356, 30974890, 29617120, 5400370],
    #[14916627, 6934151, 2943113, 23514393, 15733508, 107585, 16779023, 11649322,
      11420387, 24766737, 26624, 51968, 32559466, 32601707, 16826894, 33060453,
      4355841, 29838164, 25248170, 7422256, 33099882, 28951140, 8491174, 21030377],
    #[16739648, 23116057, 1015332, 23046791, 33514746, 20211340, 17155490, 11691911,
      26694013, 4258447, 3176448, 17811710, 12826535, 32039413, 836413, 31388165,
      6178386, 16268490, 25356039, 25006179, 32925588, 25846953, 12511032, 24740471],
    #[33057235, 21490480, 4350845, 21883840, 27971084, 7630995, 2124982, 10813078,
      31132050, 172224, 3147776, 2103390, 9102001, 16649819, 2161695, 16457223,
      20524266, 27014672, 15925855, 22219939, 28253868, 15020723, 14282562, 21853072],
    #[26509682, 23521296, 3465370, 23193664, 13489242, 4074739, 2669449, 9715366,
      12980472, 22659148, 706560, 5093552, 15034578, 33444581, 2276712, 30622555,
      3291703, 9429345, 30229687, 19370173, 31507636, 15256028, 29708757, 3735806],
    #[13710483, 6636603, 25049852, 2184325, 32759522, 19595267, 4489930, 28638906,
      26544976, 503173, 2557952, 18613461, 11892089, 11121260, 21614324, 10844083,
      22968085, 15557801, 11325062, 6074586, 33075847, 15404147, 15049340, 17158238],
    #[30135744, 5890312, 24983601, 1323560, 31064017, 19337552, 5175193, 10386409,
      9185486, 973339, 2557952, 3105304, 11203303, 25837729, 8038457, 27686270,
      7664198, 31326820, 9878453, 23451460, 15844633, 33029408, 13672625, 20759488],
    #[27733373, 1153536, 7298796, 17631273, 32039348, 17109244, 868472, 12723543,
      9503361, 19367371, 706560, 7582008, 26459477, 14027923, 18658528, 25754925,
      23339462, 11659497, 12658343, 23508282, 27164979, 27227603, 31825827, 19067527],
    #[28192483, 16955597, 24935457, 4108004, 31753447, 246012, 2823288, 15876439,
      25682657, 16896459, 3983360, 21566571, 29162155, 30207424, 19576032, 10608339,
      7452523, 27557444, 33050969, 7730071, 28877107, 27882963, 30821742, 2970905],
    #[25471911, 20913778, 502306, 4054616, 8503983, 24973470, 20461347, 13264131,
      29800279, 7801980, 4945920, 3868896, 31917461, 31524221, 23398224, 15229622,
      2949352, 12434742, 30041357, 7595912, 25191918, 13505214, 25474589, 20762931],
    #[27733354, 2359105, 20671345, 18389237, 11018577, 22344544, 19727854, 30061923,
      29610394, 24579196, 7182336, 854240, 14590475, 29947619, 5043406, 29685733,
      3884264, 26803099, 12957331, 4870262, 9652003, 32691181, 25470589, 20762931],
    #[9891834, 19557844, 22755738, 2715487, 30327989, 2719918, 19661107, 30953973,
      10466296, 119243, 1857536, 21812331, 25423369, 32292144, 713744, 10084154,
      23847737, 28557311, 14193065, 21034903, 29009016, 26095720, 31219148, 2970905],
    #[33183232, 17302305, 5516280, 24138209, 31207304, 1724640, 4863257, 15601243,
      8878940, 1334857, 3643392, 3810289, 11903829, 26789194, 21641321, 12084812,
      24884767, 28369167, 31723493, 5292717, 15205323, 14232482, 31073306, 17176418],
    #[15705293, 16962066, 25017350, 7950975, 29730934, 811232, 7684743, 31959461,
      9996482, 19200585, 3643392, 2544290, 12179046, 12276711, 6909636, 25928929,
      21280129, 26612079, 13146806, 24519341, 32351494, 14236610, 12805092, 20367202],
    #[9783313, 4305981, 4790108, 1947792, 8527767, 20782187, 6648768, 25622245,
      14375234, 20175746, 1456128, 4577512, 14186230, 12786278, 21307158, 32585014,
      18238608, 30225575, 8672979, 566761, 27854424, 30038350, 9291367, 19252722]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part14 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (14, false), (12, false), (13, true),
  (12, true), (12, true), (12, true), (13, true),
  (12, false), (13, true), (12, false), (13, true),
  (12, true), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part14.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_224 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5376 5400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_224 :
    generatedNinthLowerSpinSourceQReplayWord 6 224 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 0)
    5376 24 0 (prefix_sizes 0) slice_224
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_225 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5400 5424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_225 :
    generatedNinthLowerSpinSourceQReplayWord 6 225 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 1)
    5400 24 0 (prefix_sizes 1) slice_225
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_226 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5424 5448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_226 :
    generatedNinthLowerSpinSourceQReplayWord 6 226 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 2)
    5424 24 0 (prefix_sizes 2) slice_226
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_227 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5448 5472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_227 :
    generatedNinthLowerSpinSourceQReplayWord 6 227 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 3)
    5448 24 0 (prefix_sizes 3) slice_227
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_228 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5472 5496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_228 :
    generatedNinthLowerSpinSourceQReplayWord 6 228 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 4)
    5472 24 0 (prefix_sizes 4) slice_228
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_229 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5496 5520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_229 :
    generatedNinthLowerSpinSourceQReplayWord 6 229 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 5)
    5496 24 0 (prefix_sizes 5) slice_229
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_230 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5520 5544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_230 :
    generatedNinthLowerSpinSourceQReplayWord 6 230 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 6)
    5520 24 0 (prefix_sizes 6) slice_230
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_231 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5544 5568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_231 :
    generatedNinthLowerSpinSourceQReplayWord 6 231 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 7)
    5544 24 0 (prefix_sizes 7) slice_231
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_232 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5568 5592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_232 :
    generatedNinthLowerSpinSourceQReplayWord 6 232 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 8)
    5568 24 0 (prefix_sizes 8) slice_232
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_233 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5592 5616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_233 :
    generatedNinthLowerSpinSourceQReplayWord 6 233 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 9)
    5592 24 0 (prefix_sizes 9) slice_233
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_234 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5616 5640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_234 :
    generatedNinthLowerSpinSourceQReplayWord 6 234 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 10)
    5616 24 0 (prefix_sizes 10) slice_234
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_235 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5640 5664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_235 :
    generatedNinthLowerSpinSourceQReplayWord 6 235 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 11)
    5640 24 0 (prefix_sizes 11) slice_235
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_236 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5664 5688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_236 :
    generatedNinthLowerSpinSourceQReplayWord 6 236 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 12)
    5664 24 0 (prefix_sizes 12) slice_236
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_237 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5688 5712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_237 :
    generatedNinthLowerSpinSourceQReplayWord 6 237 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 13)
    5688 24 0 (prefix_sizes 13) slice_237
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_238 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5712 5736 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_238 :
    generatedNinthLowerSpinSourceQReplayWord 6 238 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 14)
    5712 24 0 (prefix_sizes 14) slice_238
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5712 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_239 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5736 5760 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_239 :
    generatedNinthLowerSpinSourceQReplayWord 6 239 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 15)
    5736 24 0 (prefix_sizes 15) slice_239
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5736 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_240 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 5760 5784 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_14_240 :
    generatedNinthLowerSpinSourceQReplayWord 6 240 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part14 16)
    5760 24 0 (prefix_sizes 16) slice_240
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (5760 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 224 240 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_14 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨224 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part14.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part14
    224 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (224 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
