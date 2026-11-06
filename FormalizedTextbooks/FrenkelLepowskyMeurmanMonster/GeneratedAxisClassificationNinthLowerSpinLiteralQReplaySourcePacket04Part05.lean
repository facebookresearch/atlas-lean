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
def generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 : Fin 17 → Array ℕ :=
  ![
    #[26886888, 12412835, 7123232, 28965804, 3228239, 26785689, 7101808, 10838489,
      5888784, 7953674, 17156352, 23693312, 20263472, 1808296, 715043, 6231976,
      23240088, 1873311, 4096007, 17082287, 6097683, 24218160, 45063, 11588606],
    #[12522533, 27153774, 23490675, 10881074, 2666929, 26346186, 21412931, 11195943,
      23464174, 23727047, 20957235, 22632448, 1048733, 180278, 715043, 4231222,
      7870635, 2905599, 3421524, 19354978, 25094590, 7493789, 656724, 28365822],
    #[26192686, 29933085, 17352226, 14541343, 19333039, 25885577, 3023053, 33140772,
      776352, 20348792, 23100898, 19630080, 6928002, 8008467, 2490078, 3080979,
      6507921, 19733407, 6004238, 20585757, 4954204, 3952258, 6344206, 30395288],
    #[10459982, 30310013, 268145, 31646081, 19082594, 25583322, 17498624, 31056964,
      3008704, 2697350, 6520623, 17672192, 23443377, 24764862, 4185997, 19530174,
      22826511, 18798898, 24215357, 2436739, 21862460, 20357041, 21774141, 32533606],
    #[13640646, 33272278, 23182042, 31061694, 19399965, 30713671, 17741828, 10571058,
      5243535, 4709197, 7434788, 24053760, 19697749, 4296796, 2150980, 92,
      19728393, 24023571, 5100058, 7115334, 21352977, 22153301, 7246362, 30624797],
    #[13898726, 33274358, 8252122, 13434526, 20028701, 29450087, 3651588, 12068114,
      4457103, 23780173, 21805604, 7274496, 19185749, 23445596, 2996804, 19157084,
      16844809, 8301075, 24240666, 24441414, 4254225, 5918805, 5417498, 12995645],
    #[15072231, 30953975, 7334618, 10419871, 1275165, 32528230, 7845892, 14298387,
      1313423, 22729549, 18725412, 7274496, 23513173, 6799452, 25016900, 19290204,
      4259849, 19702291, 23323162, 23394886, 5433873, 18370645, 4237850, 29707324],
    #[29834231, 32913895, 24109786, 27446927, 20034845, 31520630, 23705604, 16391427,
      19450511, 22313805, 17820196, 24053760, 5900373, 24053852, 5233220, 19830876,
      24446985, 524819, 7555610, 8165958, 6046225, 2396245, 5245466, 32326700],
    #[12778455, 33016263, 24361690, 28718767, 19410205, 32831318, 22065156, 31622435,
      20761231, 24736589, 20064804, 7274496, 22171733, 21712988, 21150276, 17481820,
      22611977, 1585683, 5206554, 23394886, 22641169, 2932821, 23869978, 33141772],
    #[12778327, 13003079, 6421210, 27516463, 17491229, 32831446, 24623108, 31722915,
      3738255, 23788365, 17048100, 24053760, 21354581, 23779420, 23368260, 19613788,
      7276553, 20746771, 6150682, 5757510, 23646737, 20660309, 25072154, 32005260],
    #[15733590, 31885638, 24376026, 32693806, 19399965, 29818839, 20428804, 25494946,
      6881935, 22737741, 5581348, 24053760, 514133, 23646300, 3445316, 2705500,
      19857417, 24023571, 22008346, 4706886, 8051217, 24725589, 7117338, 32003213],
    #[14947190, 32944486, 24095450, 33025550, 20028701, 12795895, 964612, 25976194,
      8192655, 7861069, 23650852, 7274496, 17793109, 5013596, 3799620, 17635420,
      198665, 8301075, 24373786, 6273606, 8382993, 24189013, 22063642, 32337069],
    #[9746331, 25731752, 4527985, 32216404, 20559202, 30939663, 721408, 30578833,
      2312384, 7061638, 24768303, 892928, 19535793, 20636094, 4163469, 6883774,
      5303823, 1151282, 7509821, 6669955, 155708, 24723377, 5232445, 32919731],
    #[9949494, 11269125, 22619682, 29478919, 17459119, 13703569, 19800269, 32619068,
      2443424, 24266616, 5041634, 2850816, 1492610, 4186899, 3507934, 23780115,
      22670737, 156575, 21906958, 23729437, 19173468, 4406914, 24450574, 16548224],
    #[32817686, 26964829, 21110899, 31012353, 3533233, 13184249, 4635715, 9875476,
      20465902, 19149767, 2267187, 5853184, 6951069, 6668342, 8212771, 19372086,
      23398571, 22752767, 22961492, 19545442, 7553470, 542877, 23096660, 12096973],
    #[13530917, 26702446, 6213920, 14628449, 3811919, 15493716, 23879024, 9831444,
      2583312, 505098, 960768, 6914048, 24764976, 8148904, 7188771, 20504488,
      4820376, 24841631, 24250375, 19918767, 24544019, 20798000, 21772295, 11634227],
    #[30158710, 10357156, 7210275, 14680311, 7299212, 29498294, 5634511, 9921129,
      3568695, 19490648, 5660932, 5918720, 2791700, 7012272, 5519650, 20842416,
      21647012, 17012901, 22101505, 2597297, 17825846, 3952916, 22208001, 26632519]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters04Part05 : Array GeneratedNinthLowerSpinLetter := #[
  (13, false), (12, false), (13, false), (12, false),
  (5, true), (0, true), (4, false), (5, false),
  (7, true), (0, false), (5, false), (12, true),
  (13, true), (12, true), (13, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters04Part05.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_080 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 1920 1944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_080 :
    generatedNinthLowerSpinSourceQReplayWord 4 80 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 0)
    1920 24 0 (prefix_sizes 0) slice_080
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (1920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_081 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 1944 1968 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_081 :
    generatedNinthLowerSpinSourceQReplayWord 4 81 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 1)
    1944 24 0 (prefix_sizes 1) slice_081
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (1944 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_082 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 1968 1992 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_082 :
    generatedNinthLowerSpinSourceQReplayWord 4 82 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 2)
    1968 24 0 (prefix_sizes 2) slice_082
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (1968 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_083 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 1992 2016 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_083 :
    generatedNinthLowerSpinSourceQReplayWord 4 83 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 3)
    1992 24 0 (prefix_sizes 3) slice_083
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (1992 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_084 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2016 2040 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_084 :
    generatedNinthLowerSpinSourceQReplayWord 4 84 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 4)
    2016 24 0 (prefix_sizes 4) slice_084
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2016 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_085 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2040 2064 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_085 :
    generatedNinthLowerSpinSourceQReplayWord 4 85 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 5)
    2040 24 0 (prefix_sizes 5) slice_085
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2040 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_086 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2064 2088 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_086 :
    generatedNinthLowerSpinSourceQReplayWord 4 86 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 6)
    2064 24 0 (prefix_sizes 6) slice_086
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2064 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_087 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2088 2112 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_087 :
    generatedNinthLowerSpinSourceQReplayWord 4 87 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 7)
    2088 24 0 (prefix_sizes 7) slice_087
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2088 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_088 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2112 2136 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_088 :
    generatedNinthLowerSpinSourceQReplayWord 4 88 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 8)
    2112 24 0 (prefix_sizes 8) slice_088
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2112 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_089 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2136 2160 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_089 :
    generatedNinthLowerSpinSourceQReplayWord 4 89 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 9)
    2136 24 0 (prefix_sizes 9) slice_089
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2136 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_090 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2160 2184 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_090 :
    generatedNinthLowerSpinSourceQReplayWord 4 90 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 10)
    2160 24 0 (prefix_sizes 10) slice_090
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2160 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_091 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2184 2208 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_091 :
    generatedNinthLowerSpinSourceQReplayWord 4 91 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 11)
    2184 24 0 (prefix_sizes 11) slice_091
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2184 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_092 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2208 2232 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_092 :
    generatedNinthLowerSpinSourceQReplayWord 4 92 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 12)
    2208 24 0 (prefix_sizes 12) slice_092
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2208 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_093 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2232 2256 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_093 :
    generatedNinthLowerSpinSourceQReplayWord 4 93 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 13)
    2232 24 0 (prefix_sizes 13) slice_093
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2232 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_094 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2256 2280 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_094 :
    generatedNinthLowerSpinSourceQReplayWord 4 94 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 14)
    2256 24 0 (prefix_sizes 14) slice_094
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2256 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_095 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2280 2304 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_095 :
    generatedNinthLowerSpinSourceQReplayWord 4 95 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 15)
    2280 24 0 (prefix_sizes 15) slice_095
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2280 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_096 :
    generatedNinthLowerSpinSourceQReplayPrefixWords04.extract 2304 2328 =
      generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_04_part_05_096 :
    generatedNinthLowerSpinSourceQReplayWord 4 96 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords04
    (generatedNinthLowerSpinLiteralQReplayPrefixes04Part05 16)
    2304 24 0 (prefix_sizes 16) slice_096
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords04.getD (2304 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords04.extract 80 96 =
      generatedNinthLowerSpinLiteralQReplayLetters04Part05 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_04_part_05 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 4 ⟨80 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters04Part05.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords04
    generatedNinthLowerSpinLiteralQReplayLetters04Part05
    80 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords04.getD (80 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
