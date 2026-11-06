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
def generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 : Fin 17 → Array ℕ :=
  ![
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
    #[8528814, 11435826, 4696448, 14513067, 17043236, 11038321, 2634736, 10249676,
      23720523, 3325780, 7115654, 22906880, 19413963, 8181565, 20009799, 8337213,
      24171766, 20795477, 17462435, 21695390, 24578188, 22311883, 19563683, 27510587],
    #[9411432, 30100969, 3744067, 29371801, 21075163, 12612310, 19958678, 8887933,
      2190651, 24714762, 19180357, 22255616, 412792, 19061274, 17305143, 18672154,
      18906722, 16999937, 18163811, 23628409, 22254159, 2823288, 23513187, 28598296],
    #[26846181, 12114605, 24211263, 8728700, 17901758, 10701753, 19861621, 8753622,
      19005468, 1236728, 24282425, 18581504, 19193635, 2341430, 21674772, 1632822,
      20143381, 18317319, 18058514, 1281828, 2413623, 20461347, 22207762, 15886652],
    #[10733238, 28240557, 6577650, 25419900, 18758432, 12574346, 2778840, 25225083,
      3469340, 2598965, 8254151, 17676288, 3669486, 655205, 5504234, 3456869,
      3947147, 17634644, 425951, 17438906, 1601796, 2950638, 4714463, 15222895],
    #[30582182, 8683415, 2031458, 26675665, 22874665, 8447927, 22252617, 9081816,
      17059888, 5642208, 25110388, 23074816, 21389138, 21514470, 19826258, 23791846,
      21053364, 23453198, 17281466, 6345052, 633088, 17483602, 19890618, 11746834],
    #[29802142, 31172726, 23977241, 30649934, 249812, 26438231, 3434959, 27245499,
      21547281, 7610200, 20171819, 21022720, 23958536, 385708, 2006020, 5313196,
      6446756, 20359156, 989520, 21955580, 2607116, 21015560, 5241168, 30336964],
    #[28790155, 10307795, 5962035, 26678324, 21268293, 29881611, 21278064, 25966249,
      16983233, 19336458, 21263136, 24123392, 20184562, 20289642, 4101874, 24189034,
      21650840, 17700196, 645372, 17397910, 17156864, 24778226, 3864828, 30243957],
    #[9505259, 9521632, 5912883, 26718292, 22549110, 12665195, 5143619, 10265257,
      17876492, 2407367, 5091518, 24172544, 19271487, 1838996, 149441, 6184852,
      5298347, 1212503, 17373436, 397160, 20760830, 21960511, 18618620, 13556440],
    #[32415325, 14125218, 5590510, 26196476, 4536535, 26345234, 18686157, 13565595,
      25152762, 5996408, 18874448, 21985280, 22180116, 7484549, 3967620, 2557061,
      5279121, 369935, 4327582, 5084187, 8092560, 23050516, 8108190, 9327543],
    #[16281181, 16296764, 7384867, 8616143, 7953892, 26296082, 918016, 29837573,
      4238084, 24307846, 19935280, 22001664, 24650791, 23179816, 3746889, 20075048,
      22646287, 357743, 23849824, 6357320, 5412974, 23321639, 22174560, 10212730],
    #[27868151, 13576729, 250148, 30334332, 4953680, 30271432, 505860, 29560573,
      698628, 21592909, 23443729, 19662848, 612384, 5396521, 18790863, 1296425,
      18548745, 659936, 19167721, 24041920, 4420079, 311328, 20716009, 12076065]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters05Part11 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false),
  (13, false), (12, false), (13, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters05Part11.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_176 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4224 4248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_176 :
    generatedNinthLowerSpinSourceQReplayWord 5 176 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 0)
    4224 24 0 (prefix_sizes 0) slice_176
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_177 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4248 4272 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_177 :
    generatedNinthLowerSpinSourceQReplayWord 5 177 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 1)
    4248 24 0 (prefix_sizes 1) slice_177
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4248 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_178 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4272 4296 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_178 :
    generatedNinthLowerSpinSourceQReplayWord 5 178 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 2)
    4272 24 0 (prefix_sizes 2) slice_178
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4272 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_179 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4296 4320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_179 :
    generatedNinthLowerSpinSourceQReplayWord 5 179 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 3)
    4296 24 0 (prefix_sizes 3) slice_179
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_180 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4320 4344 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_180 :
    generatedNinthLowerSpinSourceQReplayWord 5 180 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 4)
    4320 24 0 (prefix_sizes 4) slice_180
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4320 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_181 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4344 4368 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_181 :
    generatedNinthLowerSpinSourceQReplayWord 5 181 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 5)
    4344 24 0 (prefix_sizes 5) slice_181
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4344 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_182 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4368 4392 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_182 :
    generatedNinthLowerSpinSourceQReplayWord 5 182 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 6)
    4368 24 0 (prefix_sizes 6) slice_182
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4368 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_183 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4392 4416 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_183 :
    generatedNinthLowerSpinSourceQReplayWord 5 183 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 7)
    4392 24 0 (prefix_sizes 7) slice_183
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4392 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_184 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4416 4440 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_184 :
    generatedNinthLowerSpinSourceQReplayWord 5 184 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 8)
    4416 24 0 (prefix_sizes 8) slice_184
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4416 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_185 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4440 4464 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_185 :
    generatedNinthLowerSpinSourceQReplayWord 5 185 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 9)
    4440 24 0 (prefix_sizes 9) slice_185
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4440 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_186 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4464 4488 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_186 :
    generatedNinthLowerSpinSourceQReplayWord 5 186 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 10)
    4464 24 0 (prefix_sizes 10) slice_186
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4464 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_187 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4488 4512 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_187 :
    generatedNinthLowerSpinSourceQReplayWord 5 187 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 11)
    4488 24 0 (prefix_sizes 11) slice_187
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4488 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_188 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4512 4536 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_188 :
    generatedNinthLowerSpinSourceQReplayWord 5 188 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 12)
    4512 24 0 (prefix_sizes 12) slice_188
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4512 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_189 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4536 4560 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_189 :
    generatedNinthLowerSpinSourceQReplayWord 5 189 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 13)
    4536 24 0 (prefix_sizes 13) slice_189
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4536 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_190 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4560 4584 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_190 :
    generatedNinthLowerSpinSourceQReplayWord 5 190 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 14)
    4560 24 0 (prefix_sizes 14) slice_190
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4560 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_191 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4584 4608 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_191 :
    generatedNinthLowerSpinSourceQReplayWord 5 191 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 15)
    4584 24 0 (prefix_sizes 15) slice_191
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4584 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_192 :
    generatedNinthLowerSpinSourceQReplayPrefixWords05.extract 4608 4632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_05_part_11_192 :
    generatedNinthLowerSpinSourceQReplayWord 5 192 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords05
    (generatedNinthLowerSpinLiteralQReplayPrefixes05Part11 16)
    4608 24 0 (prefix_sizes 16) slice_192
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords05.getD (4608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords05.extract 176 192 =
      generatedNinthLowerSpinLiteralQReplayLetters05Part11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_05_part_11 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 5 ⟨176 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters05Part11.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords05
    generatedNinthLowerSpinLiteralQReplayLetters05Part11
    176 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords05.getD (176 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
