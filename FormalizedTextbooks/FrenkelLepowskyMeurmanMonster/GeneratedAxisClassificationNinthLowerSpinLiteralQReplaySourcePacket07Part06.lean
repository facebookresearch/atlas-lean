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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 : Fin 17 → Array ℕ :=
  ![
    #[30322051, 27188807, 22697688, 25247192, 18704496, 25941846, 398320, 30035129,
      19485461, 530260, 3122642, 7684096, 18382285, 5392699, 299545, 22126907,
      7212278, 18481163, 3403005, 7658950, 18847700, 21423565, 18023677, 14525968],
    #[16285155, 28789177, 5226613, 10320011, 20662384, 11375414, 17371150, 29964916,
      202310, 19366090, 18638719, 5480448, 18972211, 7523643, 1316473, 23532859,
      5352200, 20338008, 1101392, 22109035, 19923018, 24053299, 16791120, 13128925],
    #[30322051, 27188807, 22697688, 25247192, 18704496, 25941846, 398320, 30035129,
      19485461, 530260, 3122642, 7684096, 18382285, 5392699, 299545, 22126907,
      7212278, 18481163, 3403005, 7658950, 18847700, 21423565, 18023677, 14525968],
    #[12311118, 26747333, 6343753, 33279041, 21385937, 31368452, 20216726, 16325201,
      17083849, 19686922, 4861251, 6311936, 20949376, 22845410, 17739461, 6467554,
      6805090, 17864447, 5136541, 24207231, 2694981, 18948480, 20093085, 30411978],
    #[26088394, 29777010, 22030799, 30311363, 17534534, 25345790, 18100341, 25358089,
      1360012, 4089592, 21807297, 5697536, 21643587, 23215190, 23837572, 5858390,
      1852693, 2495383, 267906, 16904916, 17978055, 18139459, 21782146, 25599091],
    #[11437994, 16338828, 5650895, 33243406, 1170197, 9998285, 1529560, 9325146,
      20062348, 2961461, 22004236, 5648384, 21659971, 4963272, 7535738, 24572872,
      16974475, 20153658, 17745841, 17986681, 17679673, 20248899, 4607921, 12356896],
    #[30299546, 33410489, 17915248, 9981954, 1172937, 11788676, 19586121, 12683766,
      22461007, 8339424, 436996, 7897088, 2494271, 5390475, 4635693, 24184971,
      3893172, 2979809, 24596565, 22067422, 3988242, 4486975, 1931349, 12875219],
    #[32031887, 15374941, 21919011, 11162382, 20662412, 29909071, 2042319, 16249232,
      7269431, 8054616, 964868, 5918720, 5402900, 5459888, 20437282, 17282992,
      17503908, 5275813, 21198337, 17584561, 17498166, 4503828, 4234753, 25477822],
    #[32695772, 31083101, 24687907, 28066574, 1943692, 29520252, 18479567, 33239203,
      4503812, 5464262, 1190967, 7114752, 7873575, 24820782, 20188047, 3716142,
      19828745, 5580392, 4417121, 234063, 2246568, 5168167, 22462049, 12506093],
    #[13205537, 14491065, 20225392, 27082754, 20018633, 29062301, 1035337, 15469807,
      4307716, 21330754, 20212303, 6111232, 19992180, 24252539, 23853508, 7411835,
      17606159, 18163448, 8208631, 8022156, 2531248, 22476404, 18295031, 12984424],
    #[26263848, 26537868, 3967439, 16535822, 17074965, 16001199, 22542040, 10636600,
      21746188, 5817735, 22839436, 3964928, 20149187, 25095064, 8321864, 8184728,
      18694235, 5584394, 2344529, 22595017, 4161675, 18414531, 18071121, 30882722],
    #[11318395, 11349106, 19687887, 14267331, 2678342, 13121948, 6570101, 28842091,
      22995137, 25068007, 8036492, 2797568, 24846, 7429222, 6388950, 23422054,
      71016, 23024441, 3352145, 23179831, 20313560, 903438, 20139601, 32971714],
    #[10637258, 14897605, 5958729, 12229697, 7406289, 12665078, 4483990, 9891747,
      814403, 17408878, 24694217, 5926912, 20408586, 19478526, 2337579, 6975486,
      18654964, 19375647, 21324011, 651029, 4037153, 24027402, 7715051, 9361742],
    #[10901020, 11066951, 18855640, 15916504, 2840688, 10742622, 21418992, 27439281,
      1590738, 18153632, 22762261, 3186688, 2714378, 18908160, 19436330, 1080320,
      19449610, 18426976, 16841578, 19928938, 3252256, 66314, 2106218, 29601167],
    #[25535697, 8473017, 2932853, 29915275, 2967664, 27650878, 4788238, 8471164,
      19629951, 16982208, 5764678, 3186688, 17428234, 18908160, 1582922, 23552,
      2650890, 18426976, 1077098, 45930, 106560, 17929994, 18913130, 31690223],
    #[10901020, 11066951, 18855640, 15916504, 2840688, 10742622, 21418992, 27439281,
      1590738, 18153632, 22762261, 3186688, 2714378, 18908160, 19436330, 1080320,
      19449610, 18426976, 16841578, 19928938, 3252256, 66314, 2106218, 29601167],
    #[10637258, 14897605, 5958729, 12229697, 7406289, 12665078, 4483990, 9891747,
      814403, 17408878, 24694217, 5926912, 20408586, 19478526, 2337579, 6975486,
      18654964, 19375647, 21324011, 651029, 4037153, 24027402, 7715051, 9361742]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part06 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (13, false),
  (12, true), (12, true), (13, true), (12, true),
  (12, true), (13, true), (13, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part06.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_096 :
    generatedNinthLowerSpinSourceQReplayWord 7 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 0)
    2304 24 0 (prefix_sizes 0) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_097 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2328 2352 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_097 :
    generatedNinthLowerSpinSourceQReplayWord 7 97 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 1)
    2328 24 0 (prefix_sizes 1) slice_097
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2328 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_098 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2352 2376 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_098 :
    generatedNinthLowerSpinSourceQReplayWord 7 98 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 2)
    2352 24 0 (prefix_sizes 2) slice_098
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2352 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_099 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2376 2400 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_099 :
    generatedNinthLowerSpinSourceQReplayWord 7 99 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 3)
    2376 24 0 (prefix_sizes 3) slice_099
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2376 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_100 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2400 2424 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_100 :
    generatedNinthLowerSpinSourceQReplayWord 7 100 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 4)
    2400 24 0 (prefix_sizes 4) slice_100
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2400 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_101 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2424 2448 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_101 :
    generatedNinthLowerSpinSourceQReplayWord 7 101 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 5)
    2424 24 0 (prefix_sizes 5) slice_101
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2424 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_102 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2448 2472 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_102 :
    generatedNinthLowerSpinSourceQReplayWord 7 102 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 6)
    2448 24 0 (prefix_sizes 6) slice_102
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2448 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_103 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2472 2496 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_103 :
    generatedNinthLowerSpinSourceQReplayWord 7 103 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 7)
    2472 24 0 (prefix_sizes 7) slice_103
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2472 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_104 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2496 2520 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_104 :
    generatedNinthLowerSpinSourceQReplayWord 7 104 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 8)
    2496 24 0 (prefix_sizes 8) slice_104
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2496 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_105 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2520 2544 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_105 :
    generatedNinthLowerSpinSourceQReplayWord 7 105 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 9)
    2520 24 0 (prefix_sizes 9) slice_105
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2520 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_106 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2544 2568 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_106 :
    generatedNinthLowerSpinSourceQReplayWord 7 106 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 10)
    2544 24 0 (prefix_sizes 10) slice_106
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2544 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_107 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2568 2592 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_107 :
    generatedNinthLowerSpinSourceQReplayWord 7 107 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 11)
    2568 24 0 (prefix_sizes 11) slice_107
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2568 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_108 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2592 2616 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_108 :
    generatedNinthLowerSpinSourceQReplayWord 7 108 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 12)
    2592 24 0 (prefix_sizes 12) slice_108
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2592 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_109 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2616 2640 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_109 :
    generatedNinthLowerSpinSourceQReplayWord 7 109 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 13)
    2616 24 0 (prefix_sizes 13) slice_109
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2616 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_110 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2640 2664 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_110 :
    generatedNinthLowerSpinSourceQReplayWord 7 110 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 14)
    2640 24 0 (prefix_sizes 14) slice_110
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2640 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_111 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2664 2688 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_111 :
    generatedNinthLowerSpinSourceQReplayWord 7 111 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 15)
    2664 24 0 (prefix_sizes 15) slice_111
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2664 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_112 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 2688 2712 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_06_112 :
    generatedNinthLowerSpinSourceQReplayWord 7 112 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part06 16)
    2688 24 0 (prefix_sizes 16) slice_112
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (2688 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 96 112 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part06 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_06 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨96 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part06.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part06
    96 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (96 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
