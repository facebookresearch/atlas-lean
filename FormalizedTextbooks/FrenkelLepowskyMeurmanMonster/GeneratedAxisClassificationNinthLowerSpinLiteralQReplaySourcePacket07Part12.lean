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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 : Fin 17 → Array ℕ :=
  ![
    #[15435909, 26878958, 3357930, 25251281, 23168736, 16103112, 17734723, 25755159,
      20154663, 3613796, 22800721, 7090176, 23514573, 19800222, 449073, 4458654,
      4617555, 8188556, 4483039, 1847105, 3358716, 23004621, 18497503, 32312470],
    #[14171688, 9180142, 17468180, 26787375, 22172717, 15728741, 1355120, 10582409,
      16985383, 491620, 4508335, 7004160, 25116211, 19989344, 2609, 6159200,
      4236627, 7987265, 24605970, 16830066, 2804738, 21427763, 3788050, 31763304],
    #[32715389, 28171369, 17444407, 28517500, 18592890, 26404781, 20515279, 13384642,
      3174256, 4995746, 16993511, 6848512, 2980167, 4264110, 19225627, 19695790,
      24482281, 16777610, 20750435, 19425485, 23756124, 176455, 2975843, 25273262],
    #[27961758, 33315583, 20603719, 15673803, 6582981, 14989503, 2772041, 25831758,
      1425607, 2969832, 464440, 1785856, 7273344, 721120, 23443304, 18307296,
      22000480, 5812163, 17841315, 3228739, 20780264, 213888, 3953827, 15843564],
    #[16581112, 29338713, 23128712, 9438793, 982603, 30820820, 21346008, 15568271,
      20088397, 218987, 1271366, 7573504, 2196677, 21224555, 4239356, 7619691,
      5902510, 24875027, 19378365, 1971414, 1442617, 7732421, 5822653, 27581803],
    #[14128331, 9050772, 4418629, 26649161, 2599349, 16391303, 5251189, 15572463,
      2270797, 2097606, 19464981, 5599232, 3457544, 5208376, 8371202, 24699192,
      7594800, 22507840, 20087408, 16864072, 20747786, 5667336, 5057136, 10795275],
    #[15295263, 16415738, 3094488, 27407234, 23722718, 26277530, 3304342, 12325948,
      3423696, 19976774, 4152120, 3842048, 18571784, 895512, 22076764, 18584088,
      2109456, 24892801, 18056593, 4990857, 2578260, 21305864, 4427153, 30336517],
    #[11895094, 8897106, 5276457, 13196747, 6434161, 15919014, 16974832, 27841870,
      19290401, 22593155, 17314576, 1904640, 4588040, 18986547, 18875624, 2227763,
      16796731, 19291280, 18006187, 8195736, 16879328, 3848712, 2074795, 27044437],
    #[26265499, 10171137, 21677594, 15714763, 22884079, 32789446, 659470, 9172963,
      17808095, 7425309, 19333358, 2822144, 24487109, 1619405, 18903272, 20499917,
      19536136, 18238608, 3057048, 6850645, 18000941, 20962501, 17165720, 9240149],
    #[32899958, 9291765, 24098248, 30348412, 3545255, 27773061, 16777230, 29209515,
      7714376, 23568447, 376992, 4313088, 18508672, 41344, 17435298, 22706560,
      23056896, 21280129, 22804353, 4578817, 1009954, 16802688, 200577, 31961595],
    #[28506331, 14305945, 5961585, 32505391, 5987985, 11786174, 4110, 11599257,
      20170294, 24565474, 398190, 4063232, 20724039, 8141123, 21999716, 20742467,
      17369092, 20185408, 22296900, 7768071, 4534563, 17006919, 5550404, 25224557],
    #[27180520, 15351545, 21415458, 29810129, 21720817, 27654110, 20906992, 10058247,
      17408869, 23787473, 20317038, 1978368, 20745543, 8190275, 25154660, 20742467,
      20556804, 20840467, 22957079, 6081876, 7725347, 20129095, 8320023, 27907827],
    #[14946877, 27071237, 23949427, 29709358, 20535301, 11376679, 655452, 8910601,
      23984033, 7304486, 17109152, 4476928, 2129874, 2138496, 1101552, 22706560,
      6624850, 4599866, 4417128, 22597608, 3127586, 3844050, 18751080, 31973643],
    #[32384283, 31229699, 7573656, 28321915, 1036047, 27370022, 19726782, 33423953,
      2402751, 6625919, 856302, 8314880, 24293671, 6227405, 21677322, 20499917,
      17243370, 5761554, 19900152, 20740917, 25103405, 18012455, 5316344, 16653829],
    #[33425004, 31422559, 23129074, 26543000, 2240863, 29675041, 447967, 9323705,
      3879120, 2109584, 5037157, 6938624, 21599010, 19407125, 1746776, 4299029,
      3267127, 17034301, 1546, 4861727, 23592058, 25094946, 18550282, 16011861],
    #[15541409, 32856428, 22084594, 9192550, 16957791, 29675041, 18888159, 11260532,
      2953392, 1056912, 21985992, 6889472, 21594946, 17909387, 20177094, 6823563,
      19422665, 17878768, 17609529, 21577138, 5806980, 24042306, 2210617, 29685333],
    #[29760365, 33141485, 5042328, 11211805, 24915727, 27370022, 1765822, 13147097,
      376926, 5929599, 2457735, 4317184, 6572230, 18751562, 7889037, 3500106,
      2302092, 8377444, 6796520, 24198306, 7127115, 7839942, 23231720, 10791419]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part12 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, true), (12, true), (13, true),
  (12, false), (12, false), (13, false), (12, true),
  (12, true), (12, true), (13, true), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part12.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_192 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4608 4632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_192 :
    generatedNinthLowerSpinSourceQReplayWord 7 192 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 0)
    4608 24 0 (prefix_sizes 0) slice_192
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_193 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4632 4656 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_193 :
    generatedNinthLowerSpinSourceQReplayWord 7 193 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 1)
    4632 24 0 (prefix_sizes 1) slice_193
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4632 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_194 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4656 4680 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_194 :
    generatedNinthLowerSpinSourceQReplayWord 7 194 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 2)
    4656 24 0 (prefix_sizes 2) slice_194
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4656 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_195 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4680 4704 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_195 :
    generatedNinthLowerSpinSourceQReplayWord 7 195 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 3)
    4680 24 0 (prefix_sizes 3) slice_195
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4680 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_196 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4704 4728 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_196 :
    generatedNinthLowerSpinSourceQReplayWord 7 196 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 4)
    4704 24 0 (prefix_sizes 4) slice_196
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4704 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_197 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4728 4752 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_197 :
    generatedNinthLowerSpinSourceQReplayWord 7 197 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 5)
    4728 24 0 (prefix_sizes 5) slice_197
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4728 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_198 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4752 4776 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_198 :
    generatedNinthLowerSpinSourceQReplayWord 7 198 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 6)
    4752 24 0 (prefix_sizes 6) slice_198
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4752 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_199 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4776 4800 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_199 :
    generatedNinthLowerSpinSourceQReplayWord 7 199 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 7)
    4776 24 0 (prefix_sizes 7) slice_199
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4776 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_200 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4800 4824 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_200 :
    generatedNinthLowerSpinSourceQReplayWord 7 200 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 8)
    4800 24 0 (prefix_sizes 8) slice_200
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4800 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_201 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4824 4848 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_201 :
    generatedNinthLowerSpinSourceQReplayWord 7 201 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 9)
    4824 24 0 (prefix_sizes 9) slice_201
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4824 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_202 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4848 4872 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_202 :
    generatedNinthLowerSpinSourceQReplayWord 7 202 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 10)
    4848 24 0 (prefix_sizes 10) slice_202
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4848 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_203 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4872 4896 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_203 :
    generatedNinthLowerSpinSourceQReplayWord 7 203 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 11)
    4872 24 0 (prefix_sizes 11) slice_203
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4872 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_204 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4896 4920 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_204 :
    generatedNinthLowerSpinSourceQReplayWord 7 204 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 12)
    4896 24 0 (prefix_sizes 12) slice_204
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4896 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_205 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4920 4944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_205 :
    generatedNinthLowerSpinSourceQReplayWord 7 205 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 13)
    4920 24 0 (prefix_sizes 13) slice_205
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_206 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4944 4968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_206 :
    generatedNinthLowerSpinSourceQReplayWord 7 206 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 14)
    4944 24 0 (prefix_sizes 14) slice_206
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_207 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4968 4992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_207 :
    generatedNinthLowerSpinSourceQReplayWord 7 207 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 15)
    4968 24 0 (prefix_sizes 15) slice_207
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_208 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4992 5016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_12_208 :
    generatedNinthLowerSpinSourceQReplayWord 7 208 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part12 16)
    4992 24 0 (prefix_sizes 16) slice_208
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 192 208 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_12 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨192 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part12.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part12
    192 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (192 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
