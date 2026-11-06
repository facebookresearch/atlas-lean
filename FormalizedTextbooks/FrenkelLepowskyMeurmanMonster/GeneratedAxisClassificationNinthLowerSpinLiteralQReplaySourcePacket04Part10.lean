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
def generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 : Fin 16 → Array ℕ :=
  ![
    #[15659054, 9291757, 2920054, 8834383, 2431056, 14196762, 1807, 16127001,
      4802695, 1005795, 21680398, 21960704, 7039500, 23445772, 17214222, 2101516,
      5077760, 1123825, 1545969, 20944893, 6799618, 2193932, 2565873, 679143],
    #[30487472, 28427966, 3590981, 27274575, 3356720, 33023972, 378274, 31670964,
      21183956, 3492272, 21955523, 25151488, 6187201, 8384575, 437006, 20770879,
      22317310, 575087, 20014737, 1418926, 23380943, 1222849, 20039313, 457140],
    #[27368665, 31678849, 22160262, 27645138, 21035036, 11743797, 18902198, 25559005,
      24658721, 8216017, 21560385, 23123968, 22320451, 17485085, 2033666, 4775197,
      1284190, 6390009, 24412327, 24579514, 21585217, 20743491, 23351463, 3508177],
    #[8611370, 29358274, 24745931, 30374187, 517435, 10464795, 19446665, 15207462,
      22741284, 8102958, 23141848, 19773440, 20123090, 17270114, 23947534, 955746,
      1935536, 5023327, 837359, 7779213, 20804828, 24817106, 7055087, 22205734],
    #[31505267, 31996226, 4576019, 10525218, 24754763, 11009632, 21267146, 11975547,
      18075427, 3741819, 1360417, 18114560, 16803887, 17927418, 7983370, 2006266,
      22238421, 22499557, 2645040, 5775562, 7735589, 22390831, 5323824, 20322943],
    #[13986270, 31144943, 6697406, 29125489, 23084469, 11852973, 21952409, 27520470,
      18931182, 18046248, 270881, 17987584, 1743132, 20843268, 4896711, 68356,
      7393816, 5432904, 3697744, 7829332, 23043803, 6928668, 7461968, 18868705],
    #[9064893, 13492053, 21442652, 28886308, 2349405, 12030061, 17645688, 29887567,
      4185938, 1228767, 19766744, 23701504, 18241596, 22595844, 22241414, 7256324,
      7274808, 18884150, 6930190, 16778762, 19278010, 23595068, 966414, 370527],
    #[28656195, 13716070, 7811132, 8679543, 846499, 25330368, 19600504, 32640380,
      991026, 20008210, 2615435, 21583872, 2529372, 23374903, 7001976, 5430327,
      21206123, 18633573, 24731406, 832313, 3780388, 6821980, 18784014, 20346258],
    #[27248439, 9552871, 1092113, 26480430, 20479897, 16556683, 3684131, 30758435,
      23092713, 23617484, 5187504, 18561024, 22932464, 23843600, 21585707, 4895504,
      1915104, 18560792, 7071736, 23573736, 2024667, 24955888, 1128440, 20483715],
    #[9060858, 11814218, 18246257, 8531790, 18021066, 31663381, 2950638, 30062045,
      24709751, 24603730, 4256814, 17631232, 4462606, 24256750, 21821926, 5456110,
      1779936, 19022054, 24272902, 21442792, 2396648, 4524046, 20869126, 1162525],
    #[25707354, 31886301, 22556830, 26091733, 20052810, 29165154, 2883891, 31296814,
      18189200, 20241890, 469115, 21567488, 17565710, 21904485, 22185569, 7883877,
      21398635, 612197, 21617422, 20129643, 19660399, 21432334, 17554190, 3548514],
    #[12991164, 33011828, 86268, 30722936, 8138375, 31763702, 21640473, 27195775,
      1198334, 24012851, 8061848, 21956608, 137230, 1772543, 18415863, 19139583,
      5227505, 3085299, 24107010, 17957885, 23464185, 268302, 23910402, 4885754],
    #[29698065, 33016948, 16879868, 33381510, 21190937, 31267592, 24461959, 27797791,
      3894016, 23378176, 22189158, 22005760, 2833392, 2672978, 20153764, 19388754,
      4571810, 20590942, 7404540, 1970862, 24338004, 1911792, 7728124, 5491460],
    #[8526132, 32627403, 20181328, 26094485, 23755568, 26518284, 23425984, 30085182,
      24561676, 22860036, 5017598, 23730176, 21583964, 921780, 2987960, 17694900,
      4876520, 21121460, 16918876, 723432, 5070820, 21399644, 17119580, 25129484],
    #[29272856, 33461829, 7166394, 30527473, 20621328, 9543948, 19963968, 27709458,
      21354752, 24642308, 3206144, 17479680, 1964478, 18093781, 213899, 1967829,
      581483, 19089361, 2920634, 20227695, 17754677, 4057534, 6852794, 22902792],
    #[26938168, 32640613, 21563834, 33032145, 3821584, 25768236, 16777280, 11784242,
      21608704, 21605124, 3206144, 700416, 41406, 542421, 19014539, 155349,
      644971, 686033, 17080506, 50799, 20107829, 2142654, 21012666, 24145928]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters04Part10 : Array GeneratedNinthLowerSpinLetter := #[
  (13, true), (12, true), (12, true), (12, true),
  (13, true), (12, false), (13, true), (12, false),
  (13, true), (12, true), (12, true), (13, true),
  (12, true), (12, true), (5, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 16,
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters04Part10.size = 15 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_160 :
    generatedNinthLowerSpinSourceQReplayWord 4 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 0)
    3840 24 0 (prefix_sizes 0) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_161 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3864 3888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_161 :
    generatedNinthLowerSpinSourceQReplayWord 4 161 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 1)
    3864 24 0 (prefix_sizes 1) slice_161
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_162 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3888 3912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_162 :
    generatedNinthLowerSpinSourceQReplayWord 4 162 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 2)
    3888 24 0 (prefix_sizes 2) slice_162
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_163 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3912 3936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_163 :
    generatedNinthLowerSpinSourceQReplayWord 4 163 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 3)
    3912 24 0 (prefix_sizes 3) slice_163
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_164 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3936 3960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_164 :
    generatedNinthLowerSpinSourceQReplayWord 4 164 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 4)
    3936 24 0 (prefix_sizes 4) slice_164
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_165 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3960 3984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_165 :
    generatedNinthLowerSpinSourceQReplayWord 4 165 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 5)
    3960 24 0 (prefix_sizes 5) slice_165
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_166 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 3984 4008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_166 :
    generatedNinthLowerSpinSourceQReplayWord 4 166 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 6)
    3984 24 0 (prefix_sizes 6) slice_166
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (3984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_167 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4008 4032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_167 :
    generatedNinthLowerSpinSourceQReplayWord 4 167 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 7)
    4008 24 0 (prefix_sizes 7) slice_167
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_168 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4032 4056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_168 :
    generatedNinthLowerSpinSourceQReplayWord 4 168 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 8)
    4032 24 0 (prefix_sizes 8) slice_168
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_169 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4056 4080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_169 :
    generatedNinthLowerSpinSourceQReplayWord 4 169 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 9)
    4056 24 0 (prefix_sizes 9) slice_169
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_170 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4080 4104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_170 :
    generatedNinthLowerSpinSourceQReplayWord 4 170 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 10)
    4080 24 0 (prefix_sizes 10) slice_170
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_171 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4104 4128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_171 :
    generatedNinthLowerSpinSourceQReplayWord 4 171 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 11)
    4104 24 0 (prefix_sizes 11) slice_171
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_172 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4128 4152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_172 :
    generatedNinthLowerSpinSourceQReplayWord 4 172 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 12)
    4128 24 0 (prefix_sizes 12) slice_172
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_173 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4152 4176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_173 :
    generatedNinthLowerSpinSourceQReplayWord 4 173 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 13)
    4152 24 0 (prefix_sizes 13) slice_173
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_174 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4176 4200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_174 :
    generatedNinthLowerSpinSourceQReplayWord 4 174 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 14)
    4176 24 0 (prefix_sizes 14) slice_174
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_175 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 4200 4224 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_10_175 :
    generatedNinthLowerSpinSourceQReplayWord 4 175 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part10 15)
    4200 24 0 (prefix_sizes 15) slice_175
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (4200 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords04.extract 160 175 =
      generatedNinthLowerSpinLiteralQReplayLetters04Part10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_04_part_10 :
    (fun n : Fin 15 =>
      generatedNinthLowerSpinSourceQReplayLetter 4 ⟨160 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters04Part10.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords04
    generatedNinthLowerSpinLiteralQReplayLetters04Part10
    160 15 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords04.getD (160 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
