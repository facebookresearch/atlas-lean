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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 : Fin 17 → Array ℕ :=
  ![
    #[27868151, 13576729, 250148, 30334332, 4953680, 30271432, 505860, 29560573,
      698628, 21592909, 23443729, 19662848, 612384, 5396521, 18790863, 1296425,
      18548745, 659936, 19167721, 24041920, 4420079, 311328, 20716009, 12076065],
    #[16281181, 16296764, 7384867, 8616143, 7953892, 26296082, 918016, 29837573,
      4238084, 24307846, 19935280, 22001664, 24650791, 23179816, 3746889, 20075048,
      22646287, 357743, 23849824, 6357320, 5412974, 23321639, 22174560, 10212730],
    #[32415325, 14125218, 5590510, 26196476, 4536535, 26345234, 18686157, 13565595,
      25152762, 5996408, 18874448, 21985280, 22180116, 7484549, 3967620, 2557061,
      5279121, 369935, 4327582, 5084187, 8092560, 23050516, 8108190, 9327543],
    #[9505259, 9521632, 5912883, 26718292, 22549110, 12665195, 5143619, 10265257,
      17876492, 2407367, 5091518, 24172544, 19271487, 1838996, 149441, 6184852,
      5298347, 1212503, 17373436, 397160, 20760830, 21960511, 18618620, 13556440],
    #[28790155, 10307795, 5962035, 26678324, 21268293, 29881611, 21278064, 25966249,
      16983233, 19336458, 21263136, 24123392, 20184562, 20289642, 4101874, 24189034,
      21650840, 17700196, 645372, 17397910, 17156864, 24778226, 3864828, 30243957],
    #[29802142, 31172726, 23977241, 30649934, 249812, 26438231, 3434959, 27245499,
      21547281, 7610200, 20171819, 21022720, 23958536, 385708, 2006020, 5313196,
      6446756, 20359156, 989520, 21955580, 2607116, 21015560, 5241168, 30336964],
    #[30582182, 8683415, 2031458, 26675665, 22874665, 8447927, 22252617, 9081816,
      17059888, 5642208, 25110388, 23074816, 21389138, 21514470, 19826258, 23791846,
      21053364, 23453198, 17281466, 6345052, 633088, 17483602, 19890618, 11746834],
    #[10733238, 28240557, 6577650, 25419900, 18758432, 12574346, 2778840, 25225083,
      3469340, 2598965, 8254151, 17676288, 3669486, 655205, 5504234, 3456869,
      3947147, 17634644, 425951, 17438906, 1601796, 2950638, 4714463, 15222895],
    #[26846181, 12114605, 24211263, 8728700, 17901758, 10701753, 19861621, 8753622,
      19005468, 1236728, 24282425, 18581504, 19193635, 2341430, 21674772, 1632822,
      20143381, 18317319, 18058514, 1281828, 2413623, 20461347, 22207762, 15886652],
    #[9411432, 30100969, 3744067, 29371801, 21075163, 12612310, 19958678, 8887933,
      2190651, 24714762, 19180357, 22255616, 412792, 19061274, 17305143, 18672154,
      18906722, 16999937, 18163811, 23628409, 22254159, 2823288, 23513187, 28598296],
    #[8528814, 11435826, 4696448, 14513067, 17043236, 11038321, 2634736, 10249676,
      23720523, 3325780, 7115654, 22906880, 19413963, 8181565, 20009799, 8337213,
      24171766, 20795477, 17462435, 21695390, 24578188, 22311883, 19563683, 27510587],
    #[28586958, 10403666, 21719219, 15652198, 17676474, 26123793, 17235982, 11965599,
      20997557, 19605706, 21628806, 24864768, 879878, 24122894, 1361290, 23447054,
      25125640, 4073112, 423312, 6159262, 7800972, 6804742, 2524560, 8421878],
    #[31593097, 14537736, 19653805, 12657681, 53596, 31554359, 659470, 25907826,
      3813725, 21748621, 21597371, 23357440, 17815024, 19931124, 20879295, 20561908,
      20173316, 135049, 3730829, 6298233, 5476943, 19537392, 4918669, 16378256],
    #[11887802, 11169266, 24303725, 9292595, 16831484, 28159206, 16777230, 12497371,
      17001473, 1537466, 776543, 22206464, 17171564, 18877796, 22941787, 17239396,
      7147784, 21658440, 2509376, 20557604, 19190839, 19975276, 6756928, 14201459],
    #[10281764, 9408319, 22100672, 10414590, 4128770, 25492248, 984048, 12113371,
      19967660, 3466007, 19605855, 23336960, 443500, 3971159, 5551464, 1808471,
      6796347, 6552790, 17131757, 2500794, 18379012, 3148908, 21297389, 15811053],
    #[14177835, 33165635, 205124, 29565274, 19583246, 15806263, 16826460, 9721376,
      18326708, 7932470, 7081147, 21080064, 3134960, 16965311, 17569524, 17530559,
      86863, 3689259, 3156068, 6266587, 23384836, 663024, 6539364, 14268768],
    #[12699260, 32332160, 1220481, 32998324, 7149834, 9558595, 655806, 32579965,
      23491207, 20085274, 5785478, 17946624, 21683462, 23286926, 25130762, 24544398,
      1364360, 21746474, 1585826, 331308, 3258892, 18900230, 8352418, 11915686]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part12 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (13, true),
  (12, true), (12, true), (12, true), (13, true),
  (12, true), (12, true), (13, true), (12, false),
  (12, false), (13, false), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part12.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_192 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4608 4632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_192 :
    generatedNinthLowerSpinSourceQReplayWord 5 192 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 0)
    4608 24 0 (prefix_sizes 0) slice_192
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_193 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4632 4656 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_193 :
    generatedNinthLowerSpinSourceQReplayWord 5 193 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 1)
    4632 24 0 (prefix_sizes 1) slice_193
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4632 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_194 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4656 4680 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_194 :
    generatedNinthLowerSpinSourceQReplayWord 5 194 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 2)
    4656 24 0 (prefix_sizes 2) slice_194
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4656 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_195 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4680 4704 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_195 :
    generatedNinthLowerSpinSourceQReplayWord 5 195 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 3)
    4680 24 0 (prefix_sizes 3) slice_195
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4680 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_196 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4704 4728 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_196 :
    generatedNinthLowerSpinSourceQReplayWord 5 196 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 4)
    4704 24 0 (prefix_sizes 4) slice_196
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4704 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_197 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4728 4752 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_197 :
    generatedNinthLowerSpinSourceQReplayWord 5 197 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 5)
    4728 24 0 (prefix_sizes 5) slice_197
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4728 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_198 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4752 4776 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_198 :
    generatedNinthLowerSpinSourceQReplayWord 5 198 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 6)
    4752 24 0 (prefix_sizes 6) slice_198
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4752 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_199 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4776 4800 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_199 :
    generatedNinthLowerSpinSourceQReplayWord 5 199 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 7)
    4776 24 0 (prefix_sizes 7) slice_199
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4776 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_200 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4800 4824 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_200 :
    generatedNinthLowerSpinSourceQReplayWord 5 200 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 8)
    4800 24 0 (prefix_sizes 8) slice_200
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4800 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_201 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4824 4848 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_201 :
    generatedNinthLowerSpinSourceQReplayWord 5 201 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 9)
    4824 24 0 (prefix_sizes 9) slice_201
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4824 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_202 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4848 4872 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_202 :
    generatedNinthLowerSpinSourceQReplayWord 5 202 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 10)
    4848 24 0 (prefix_sizes 10) slice_202
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4848 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_203 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4872 4896 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_203 :
    generatedNinthLowerSpinSourceQReplayWord 5 203 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 11)
    4872 24 0 (prefix_sizes 11) slice_203
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4872 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_204 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4896 4920 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_204 :
    generatedNinthLowerSpinSourceQReplayWord 5 204 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 12)
    4896 24 0 (prefix_sizes 12) slice_204
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4896 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_205 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4920 4944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_205 :
    generatedNinthLowerSpinSourceQReplayWord 5 205 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 13)
    4920 24 0 (prefix_sizes 13) slice_205
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_206 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4944 4968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_206 :
    generatedNinthLowerSpinSourceQReplayWord 5 206 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 14)
    4944 24 0 (prefix_sizes 14) slice_206
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_207 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4968 4992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_207 :
    generatedNinthLowerSpinSourceQReplayWord 5 207 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 15)
    4968 24 0 (prefix_sizes 15) slice_207
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_208 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4992 5016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_12_208 :
    generatedNinthLowerSpinSourceQReplayWord 5 208 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part12 16)
    4992 24 0 (prefix_sizes 16) slice_208
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 192 208 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_12 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨192 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part12.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part12
    192 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (192 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
