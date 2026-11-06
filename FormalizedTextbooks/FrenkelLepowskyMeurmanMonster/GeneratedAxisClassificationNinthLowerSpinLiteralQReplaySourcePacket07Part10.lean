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
def generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 : Fin 17 → Array ℕ :=
  ![
    #[14254113, 9613235, 18453319, 9256962, 23834059, 8713274, 22862921, 32122432,
      21829902, 22144466, 17869946, 1589248, 4436553, 17693396, 7998812, 582356,
      2826397, 2220237, 2953296, 8323716, 2889493, 3426889, 23963728, 14870109],
    #[31306024, 26451082, 21457544, 28385550, 975387, 33484352, 5408472, 13246943,
      303370, 19722287, 2652869, 7442432, 168834, 24729471, 4891880, 8277887,
      4308221, 23903299, 17739966, 1617857, 18390890, 6581122, 5531838, 27509227],
    #[16200827, 9050996, 4512837, 25310147, 19375493, 31263981, 22491253, 30024159,
      1124295, 284, 19799749, 4276224, 1336194, 24925650, 7090408, 7040466,
      5529168, 5270896, 107296, 1212146, 527210, 4344706, 21859104, 10724747],
    #[11653066, 15867541, 8120280, 27860033, 21178000, 29592630, 24538006, 25536626,
      3973651, 2647103, 5890585, 7991296, 18132427, 20484143, 3311467, 7981103,
      1975780, 18155983, 5557291, 3736580, 1970848, 22996427, 22344747, 11531934],
    #[11654684, 16536231, 3924777, 31808984, 2985384, 32122688, 984048, 26793367,
      1218866, 3901775, 3146556, 3006464, 5124635, 3264806, 4441085, 21117222,
      3943229, 6683721, 3577716, 24497746, 16849382, 7461403, 24424308, 11074982],
    #[25298129, 31655257, 18310682, 13621387, 510203, 32752862, 16777230, 11432439,
      490399, 18577743, 1032354, 770048, 22521221, 173963, 21959342, 22523787,
      17832462, 4635268, 3743882, 22011649, 159531, 21527941, 21878922, 12303115],
    #[32117180, 28127987, 25105864, 16713648, 2768225, 28024399, 4110, 9303661,
      7959940, 22774847, 3735648, 7405568, 2517068, 17850438, 3586916, 6735942,
      8323082, 22577223, 21454925, 7948299, 18840360, 2146380, 206925, 30140151],
    #[13631727, 11665773, 7581851, 30467118, 19263231, 27549105, 20906992, 9299469,
      23404727, 4695308, 594016, 5369856, 18262060, 19863512, 597146, 6909912,
      20998132, 5432692, 4371072, 5492056, 2100406, 17825836, 16788096, 16028009],
    #[26185565, 31814928, 22981760, 26901969, 4553623, 10604625, 4594582, 32924423,
      1430945, 18814194, 6027745, 5079040, 17256737, 16800837, 326787, 6181957,
      17134948, 4830255, 25117003, 6120718, 22070690, 19290401, 1407307, 27823132],
    #[27307003, 27006146, 21272241, 25983408, 6991752, 9371405, 4018293, 8515063,
      24726369, 20539246, 17672031, 6496256, 7730640, 645839, 22936130, 20017871,
      2438943, 115244, 8369459, 19904508, 21014418, 3423696, 24333619, 9826254],
    #[28704086, 28698460, 23373489, 26630371, 22222966, 28634718, 18745048, 25647511,
      6515250, 3762030, 18761106, 5627904, 25113731, 16779569, 23587601, 1610033,
      3589554, 20054145, 4814131, 17410, 21014418, 19799171, 23309619, 27525038],
    #[10002150, 29697504, 22752384, 10332266, 7372695, 10716650, 5556781, 29587447,
      1179674, 2036978, 24771754, 6832128, 19256474, 3120151, 17213752, 24384535,
      2973837, 6562246, 22708555, 24261980, 22070690, 18975898, 3156299, 10968254],
    #[26536917, 30405843, 23981184, 26480532, 24447290, 8786727, 21244461, 29364570,
      3905508, 3204876, 6732596, 4763648, 3953508, 3475780, 707691, 24670532,
      20861472, 7452523, 21632331, 4727823, 24373007, 920420, 417099, 11030304],
    #[12775238, 14889650, 18929329, 29484165, 38943, 25327574, 5408472, 9488894,
      24655444, 20774134, 5738517, 2490368, 5966053, 23687872, 17170656, 7961280,
      524837, 2949352, 6234829, 4196365, 4259845, 7426277, 21105357, 29588951],
    #[30702374, 16323553, 19269297, 30700072, 20597068, 11801526, 22491253, 8645427,
      8081657, 19249928, 22161080, 3547136, 21532232, 24805485, 18227424, 8038509,
      17720869, 3884264, 22672077, 4573856, 5543592, 23381576, 5434061, 31668695],
    #[27569957, 13115752, 21560448, 10690095, 22502529, 9689047, 24538006, 12719121,
      2934367, 18899724, 5569167, 5103616, 938719, 18685101, 1023083, 5584045,
      18962034, 23847737, 7275851, 23097830, 4519604, 3742431, 19074379, 28826482],
    #[15112054, 26313382, 4399259, 15672444, 20757908, 11705896, 984048, 11461990,
      23077093, 6136076, 245952, 6365184, 1276030, 19697843, 16829425, 6338739,
      24912077, 24884767, 5760722, 21352033, 1874831, 3100798, 18874066, 14747035]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters07Part10 : Array GeneratedNinthLowerSpinLetter := #[
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (12, false), (13, false), (12, false),
  (12, false), (13, false), (12, true), (13, false),
  (12, false), (13, true), (12, true), (12, true)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters07Part10.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_160 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3840 3864 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_160 :
    generatedNinthLowerSpinSourceQReplayWord 7 160 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 0)
    3840 24 0 (prefix_sizes 0) slice_160
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3840 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_161 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3864 3888 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_161 :
    generatedNinthLowerSpinSourceQReplayWord 7 161 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 1)
    3864 24 0 (prefix_sizes 1) slice_161
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3864 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_162 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3888 3912 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_162 :
    generatedNinthLowerSpinSourceQReplayWord 7 162 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 2)
    3888 24 0 (prefix_sizes 2) slice_162
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3888 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_163 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3912 3936 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_163 :
    generatedNinthLowerSpinSourceQReplayWord 7 163 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 3)
    3912 24 0 (prefix_sizes 3) slice_163
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3912 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_164 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3936 3960 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_164 :
    generatedNinthLowerSpinSourceQReplayWord 7 164 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 4)
    3936 24 0 (prefix_sizes 4) slice_164
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3936 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_165 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3960 3984 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_165 :
    generatedNinthLowerSpinSourceQReplayWord 7 165 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 5)
    3960 24 0 (prefix_sizes 5) slice_165
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3960 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_166 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 3984 4008 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_166 :
    generatedNinthLowerSpinSourceQReplayWord 7 166 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 6)
    3984 24 0 (prefix_sizes 6) slice_166
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (3984 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_167 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4008 4032 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_167 :
    generatedNinthLowerSpinSourceQReplayWord 7 167 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 7)
    4008 24 0 (prefix_sizes 7) slice_167
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4008 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_168 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4032 4056 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_168 :
    generatedNinthLowerSpinSourceQReplayWord 7 168 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 8)
    4032 24 0 (prefix_sizes 8) slice_168
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4032 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_169 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4056 4080 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_169 :
    generatedNinthLowerSpinSourceQReplayWord 7 169 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 9)
    4056 24 0 (prefix_sizes 9) slice_169
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4056 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_170 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4080 4104 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_170 :
    generatedNinthLowerSpinSourceQReplayWord 7 170 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 10)
    4080 24 0 (prefix_sizes 10) slice_170
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4080 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_171 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4104 4128 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_171 :
    generatedNinthLowerSpinSourceQReplayWord 7 171 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 11)
    4104 24 0 (prefix_sizes 11) slice_171
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4104 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_172 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4128 4152 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_172 :
    generatedNinthLowerSpinSourceQReplayWord 7 172 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 12)
    4128 24 0 (prefix_sizes 12) slice_172
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4128 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_173 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4152 4176 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_173 :
    generatedNinthLowerSpinSourceQReplayWord 7 173 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 13)
    4152 24 0 (prefix_sizes 13) slice_173
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4152 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_174 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4176 4200 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_174 :
    generatedNinthLowerSpinSourceQReplayWord 7 174 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 14)
    4176 24 0 (prefix_sizes 14) slice_174
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4176 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_175 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4200 4224 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_175 :
    generatedNinthLowerSpinSourceQReplayWord 7 175 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 15)
    4200 24 0 (prefix_sizes 15) slice_175
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4200 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_176 :
    generatedNinthLowerSpinSourceQReplayPrefixWords07.extract 4224 4248 =
      generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_07_part_10_176 :
    generatedNinthLowerSpinSourceQReplayWord 7 176 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords07
    (generatedNinthLowerSpinLiteralQReplayPrefixes07Part10 16)
    4224 24 0 (prefix_sizes 16) slice_176
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords07.getD (4224 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords07.extract 160 176 =
      generatedNinthLowerSpinLiteralQReplayLetters07Part10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_07_part_10 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 7 ⟨160 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters07Part10.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords07
    generatedNinthLowerSpinLiteralQReplayLetters07Part10
    160 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords07.getD (160 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
