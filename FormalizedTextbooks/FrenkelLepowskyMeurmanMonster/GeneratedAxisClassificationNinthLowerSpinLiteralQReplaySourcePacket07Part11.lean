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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 : Fin 17 → Array ℕ :=
  ![
    #[15112054, 26313382, 4399259, 15672444, 20757908, 11705896, 984048, 11461990,
      23077093, 6136076, 245952, 6365184, 1276030, 19697843, 16829425, 6338739,
      24912077, 24884767, 5760722, 21352033, 1874831, 3100798, 18874066, 14747035],
    #[32899958, 9291765, 24098248, 30348412, 3545255, 27773061, 16777230, 29209515,
      7714376, 23568447, 376992, 4313088, 18508672, 41344, 17435298, 22706560,
      23056896, 21280129, 22804353, 4578817, 1009954, 16802688, 200577, 31961595],
    #[26265499, 10171137, 21677594, 15714763, 22884079, 32789446, 659470, 9172963,
      17808095, 7425309, 19333358, 2822144, 24487109, 1619405, 18903272, 20499917,
      19536136, 18238608, 3057048, 6850645, 18000941, 20962501, 17165720, 9240149],
    #[11895094, 8897106, 5276457, 13196747, 6434161, 15919014, 16974832, 27841870,
      19290401, 22593155, 17314576, 1904640, 4588040, 18986547, 18875624, 2227763,
      16796731, 19291280, 18006187, 8195736, 16879328, 3848712, 2074795, 27044437],
    #[15295263, 16415738, 3094488, 27407234, 23722718, 26277530, 3304342, 12325948,
      3423696, 19976774, 4152120, 3842048, 18571784, 895512, 22076764, 18584088,
      2109456, 24892801, 18056593, 4990857, 2578260, 21305864, 4427153, 30336517],
    #[14128331, 9050772, 4418629, 26649161, 2599349, 16391303, 5251189, 15572463,
      2270797, 2097606, 19464981, 5599232, 3457544, 5208376, 8371202, 24699192,
      7594800, 22507840, 20087408, 16864072, 20747786, 5667336, 5057136, 10795275],
    #[16581112, 29338713, 23128712, 9438793, 982603, 30820820, 21346008, 15568271,
      20088397, 218987, 1271366, 7573504, 2196677, 21224555, 4239356, 7619691,
      5902510, 24875027, 19378365, 1971414, 1442617, 7732421, 5822653, 27581803],
    #[27961758, 33315583, 20603719, 15673803, 6582981, 14989503, 2772041, 25831758,
      1425607, 2969832, 464440, 1785856, 7273344, 721120, 23443304, 18307296,
      22000480, 5812163, 17841315, 3228739, 20780264, 213888, 3953827, 15843564],
    #[32715389, 28171369, 17444407, 28517500, 18592890, 26404781, 20515279, 13384642,
      3174256, 4995746, 16993511, 6848512, 2980167, 4264110, 19225627, 19695790,
      24482281, 16777610, 20750435, 19425485, 23756124, 176455, 2975843, 25273262],
    #[14171688, 9180142, 17468180, 26787375, 22172717, 15728741, 1355120, 10582409,
      16985383, 491620, 4508335, 7004160, 25116211, 19989344, 2609, 6159200,
      4236627, 7987265, 24605970, 16830066, 2804738, 21427763, 3788050, 31763304],
    #[15435909, 26878958, 3357930, 25251281, 23168736, 16103112, 17734723, 25755159,
      20154663, 3613796, 22800721, 7090176, 23514573, 19800222, 449073, 4458654,
      4617555, 8188556, 4483039, 1847105, 3358716, 23004621, 18497503, 32312470],
    #[28243902, 25962664, 22959698, 29288880, 6852436, 10153849, 3014861, 27304245,
      6440914, 17803027, 17671937, 4714496, 23255424, 19733105, 23246568, 3076721,
      19852273, 19792459, 21281210, 17353675, 25098088, 18915712, 6631866, 8646531],
    #[11462622, 27946184, 24278785, 26396899, 7850186, 11958826, 18547200, 12183243,
      5527474, 1738174, 18957906, 4665344, 7874739, 4057617, 7811109, 19411473,
      17046178, 480693, 24239895, 19766534, 21057686, 2924723, 4224791, 8453422],
    #[30570055, 9695101, 2502667, 30184541, 805773, 9909031, 20842500, 33043338,
      5323942, 18450338, 2595844, 602112, 5219501, 24513737, 19963088, 8365257,
      17277028, 20119901, 7266617, 8140272, 6361213, 5323949, 24484153, 15336925],
    #[11462622, 27946184, 24278785, 26396899, 7850186, 11958826, 18547200, 12183243,
      5527474, 1738174, 18957906, 4665344, 7874739, 4057617, 7811109, 19411473,
      17046178, 480693, 24239895, 19766534, 21057686, 2924723, 4224791, 8453422],
    #[28243902, 25962664, 22959698, 29288880, 6852436, 10153849, 3014861, 27304245,
      6440914, 17803027, 17671937, 4714496, 23255424, 19733105, 23246568, 3076721,
      19852273, 19792459, 21281210, 17353675, 25098088, 18915712, 6631866, 8646531],
    #[15435909, 26878958, 3357930, 25251281, 23168736, 16103112, 17734723, 25755159,
      20154663, 3613796, 22800721, 7090176, 23514573, 19800222, 449073, 4458654,
      4617555, 8188556, 4483039, 1847105, 3358716, 23004621, 18497503, 32312470]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part11 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (13, false), (12, false),
  (12, false), (13, false), (12, false), (12, false),
  (12, false), (13, false), (12, false), (13, false),
  (12, false), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part11.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_176 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4224 4248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_176 :
    generatedNinthLowerSpinSourceQReplayWord 7 176 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 0)
    4224 24 0 (prefix_sizes 0) slice_176
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_177 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4248 4272 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_177 :
    generatedNinthLowerSpinSourceQReplayWord 7 177 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 1)
    4248 24 0 (prefix_sizes 1) slice_177
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4248 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_178 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4272 4296 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_178 :
    generatedNinthLowerSpinSourceQReplayWord 7 178 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 2)
    4272 24 0 (prefix_sizes 2) slice_178
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4272 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_179 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4296 4320 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_179 :
    generatedNinthLowerSpinSourceQReplayWord 7 179 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 3)
    4296 24 0 (prefix_sizes 3) slice_179
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4296 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_180 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4320 4344 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_180 :
    generatedNinthLowerSpinSourceQReplayWord 7 180 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 4)
    4320 24 0 (prefix_sizes 4) slice_180
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4320 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_181 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4344 4368 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_181 :
    generatedNinthLowerSpinSourceQReplayWord 7 181 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 5)
    4344 24 0 (prefix_sizes 5) slice_181
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4344 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_182 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4368 4392 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_182 :
    generatedNinthLowerSpinSourceQReplayWord 7 182 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 6)
    4368 24 0 (prefix_sizes 6) slice_182
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4368 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_183 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4392 4416 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_183 :
    generatedNinthLowerSpinSourceQReplayWord 7 183 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 7)
    4392 24 0 (prefix_sizes 7) slice_183
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4392 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_184 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4416 4440 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_184 :
    generatedNinthLowerSpinSourceQReplayWord 7 184 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 8)
    4416 24 0 (prefix_sizes 8) slice_184
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4416 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_185 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4440 4464 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_185 :
    generatedNinthLowerSpinSourceQReplayWord 7 185 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 9)
    4440 24 0 (prefix_sizes 9) slice_185
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4440 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_186 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4464 4488 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_186 :
    generatedNinthLowerSpinSourceQReplayWord 7 186 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 10)
    4464 24 0 (prefix_sizes 10) slice_186
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4464 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_187 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4488 4512 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_187 :
    generatedNinthLowerSpinSourceQReplayWord 7 187 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 11)
    4488 24 0 (prefix_sizes 11) slice_187
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4488 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_188 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4512 4536 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_188 :
    generatedNinthLowerSpinSourceQReplayWord 7 188 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 12)
    4512 24 0 (prefix_sizes 12) slice_188
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4512 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_189 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4536 4560 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_189 :
    generatedNinthLowerSpinSourceQReplayWord 7 189 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 13)
    4536 24 0 (prefix_sizes 13) slice_189
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4536 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_190 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4560 4584 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_190 :
    generatedNinthLowerSpinSourceQReplayWord 7 190 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 14)
    4560 24 0 (prefix_sizes 14) slice_190
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4560 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_191 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4584 4608 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_191 :
    generatedNinthLowerSpinSourceQReplayWord 7 191 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 15)
    4584 24 0 (prefix_sizes 15) slice_191
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4584 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_192 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4608 4632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_11_192 :
    generatedNinthLowerSpinSourceQReplayWord 7 192 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part11 16)
    4608 24 0 (prefix_sizes 16) slice_192
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 176 192 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_11 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨176 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part11.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part11
    176 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (176 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
