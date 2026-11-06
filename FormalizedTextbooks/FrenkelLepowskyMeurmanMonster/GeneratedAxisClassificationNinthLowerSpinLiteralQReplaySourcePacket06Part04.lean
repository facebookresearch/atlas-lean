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
def generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 : Fin 17 → Array ℕ :=
  ![
    #[32843531, 12812719, 24627663, 32380717, 80661, 31798924, 5891800, 15975195,
      22796812, 20712839, 4802700, 20744192, 23608259, 20937624, 17232712, 20806552,
      497755, 3302922, 22955601, 6610377, 18663563, 21214147, 24000081, 12694913],
    #[31791369, 32230545, 2342256, 11450666, 6120905, 30647733, 21486665, 15592903,
      7406340, 8233794, 3330639, 22890496, 18257524, 22683771, 1610180, 22618235,
      200207, 21616376, 19796215, 16842892, 24274864, 24211060, 21262583, 8573248],
    #[32108029, 32033404, 79139, 13957935, 18442380, 13128029, 5634511, 12574850,
      1167620, 23005382, 20722743, 23894016, 5557287, 20601902, 6054799, 24665134,
      4364297, 1943144, 23586401, 23591503, 23515048, 6435879, 24262241, 11731916],
    #[14691939, 33286321, 1508643, 31975906, 1681548, 12681891, 22411727, 8401788,
      2978871, 21008216, 18915588, 22697984, 4757780, 217008, 7299362, 5750704,
      4325028, 1622181, 4314625, 6224305, 4806710, 6181140, 4339201, 9097298],
    #[12634617, 15321562, 2358640, 11091041, 24995273, 33318375, 4709449, 13102485,
      21381711, 21112800, 16782084, 24676352, 284479, 6234251, 18154541, 8151179,
      18112436, 5343201, 2396245, 921822, 21836562, 6696767, 5156949, 10998192],
    #[9799515, 31119229, 17775055, 27439615, 21400341, 11048764, 22669016, 9659051,
      18704524, 23394357, 5900812, 22427648, 20760899, 3308488, 23549050, 998344,
      821899, 18048314, 2205617, 4512889, 7220537, 21147971, 6891441, 9110993],
    #[10936726, 30803502, 2742735, 26374559, 8138310, 12018850, 4874357, 25965909,
      3901580, 21462776, 8333505, 22476800, 18676035, 18562134, 6824836, 18902102,
      20184341, 3597207, 20665986, 4700884, 4684487, 21131587, 24319618, 8701487],
    #[16196344, 25874803, 21834825, 28439799, 5391057, 14554546, 60310, 11893479,
      20047305, 6925834, 19580227, 23091200, 19333504, 18040802, 6178501, 19757026,
      19967586, 20961023, 20336797, 4634495, 23156549, 20547968, 21667997, 13409404],
    #[26968664, 26053020, 3987160, 33231363, 1448048, 15601805, 17966064, 13470562,
      22440725, 23400276, 20983250, 24463360, 16893389, 3295547, 23190041, 3254587,
      18330870, 19873803, 25107709, 22554054, 6516692, 23027149, 23067901, 28651979],
    #[12502261, 25647279, 18452597, 30732701, 1448048, 16511520, 725006, 13343586,
      7130694, 4999370, 7548799, 22259712, 18413107, 3292475, 21470841, 2616635,
      19452680, 19215704, 24829520, 8106859, 5900362, 22449715, 23735888, 26572235],
    #[26968664, 26053020, 3987160, 33231363, 1448048, 15601805, 17966064, 13470562,
      22440725, 23400276, 20983250, 24463360, 16893389, 3295547, 23190041, 3254587,
      18330870, 19873803, 25107709, 22554054, 6516692, 23027149, 23067901, 28651979],
    #[16196344, 25874803, 21834825, 28439799, 5391057, 14554546, 60310, 11893479,
      20047305, 6925834, 19580227, 23091200, 19333504, 18040802, 6178501, 19757026,
      19967586, 20961023, 20336797, 4634495, 23156549, 20547968, 21667997, 13409404],
    #[10936726, 30803502, 2742735, 26374559, 8138310, 12018850, 4874357, 25965909,
      3901580, 21462776, 8333505, 22476800, 18676035, 18562134, 6824836, 18902102,
      20184341, 3597207, 20665986, 4700884, 4684487, 21131587, 24319618, 8701487],
    #[9799515, 31119229, 17775055, 27439615, 21400341, 11048764, 22669016, 9659051,
      18704524, 23394357, 5900812, 22427648, 20760899, 3308488, 23549050, 998344,
      821899, 18048314, 2205617, 4512889, 7220537, 21147971, 6891441, 9110993],
    #[12634617, 15321562, 2358640, 11091041, 24995273, 33318375, 4709449, 13102485,
      21381711, 21112800, 16782084, 24676352, 284479, 6234251, 18154541, 8151179,
      18112436, 5343201, 2396245, 921822, 21836562, 6696767, 5156949, 10998192],
    #[14691939, 33286321, 1508643, 31975906, 1681548, 12681891, 22411727, 8401788,
      2978871, 21008216, 18915588, 22697984, 4757780, 217008, 7299362, 5750704,
      4325028, 1622181, 4314625, 6224305, 4806710, 6181140, 4339201, 9097298],
    #[26886888, 12412835, 7123232, 28965804, 3228239, 26785689, 7101808, 10838489,
      5888784, 7953674, 17156352, 23693312, 20263472, 1808296, 715043, 6231976,
      23240088, 1873311, 4096007, 17082287, 6097683, 24218160, 45063, 11588606]
  ]

/-- Precisely the original signed primitives, in chronological order. -/
def generatedNinthLowerSpinLiteralQReplayLetters06Part04 : Array GeneratedNinthLowerSpinLetter := #[
  (12, false), (12, false), (13, true), (12, true),
  (12, true), (13, true), (12, true), (12, true),
  (13, true), (13, false), (12, false), (12, false),
  (13, false), (12, false), (12, false), (12, false)
]

/-- Each full prefix has exactly the original twenty-four coordinates. -/
private theorem prefix_sizes : ∀ n : Fin 17,
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 n).size = 24 := by
  decide +kernel

/-- The full source letter chunk has its actual original length. -/
private theorem letter_size : generatedNinthLowerSpinLiteralQReplayLetters06Part04.size = 16 := rfl

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_064 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1536 1560 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 0 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_064 :
    generatedNinthLowerSpinSourceQReplayWord 6 64 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 0).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 0)
    1536 24 0 (prefix_sizes 0) slice_064
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1536 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_065 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1560 1584 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_065 :
    generatedNinthLowerSpinSourceQReplayWord 6 65 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 1).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 1)
    1560 24 0 (prefix_sizes 1) slice_065
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1560 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_066 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1584 1608 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 2 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_066 :
    generatedNinthLowerSpinSourceQReplayWord 6 66 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 2).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 2)
    1584 24 0 (prefix_sizes 2) slice_066
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1584 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_067 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1608 1632 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 3 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_067 :
    generatedNinthLowerSpinSourceQReplayWord 6 67 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 3).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 3)
    1608 24 0 (prefix_sizes 3) slice_067
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1608 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_068 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1632 1656 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 4 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_068 :
    generatedNinthLowerSpinSourceQReplayWord 6 68 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 4).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 4)
    1632 24 0 (prefix_sizes 4) slice_068
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1632 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_069 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1656 1680 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 5 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_069 :
    generatedNinthLowerSpinSourceQReplayWord 6 69 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 5).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 5)
    1656 24 0 (prefix_sizes 5) slice_069
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1656 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_070 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1680 1704 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 6 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_070 :
    generatedNinthLowerSpinSourceQReplayWord 6 70 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 6).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 6)
    1680 24 0 (prefix_sizes 6) slice_070
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1680 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_071 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1704 1728 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 7 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_071 :
    generatedNinthLowerSpinSourceQReplayWord 6 71 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 7).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 7)
    1704 24 0 (prefix_sizes 7) slice_071
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1704 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_072 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1728 1752 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 8 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_072 :
    generatedNinthLowerSpinSourceQReplayWord 6 72 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 8).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 8)
    1728 24 0 (prefix_sizes 8) slice_072
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1728 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_073 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1752 1776 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 9 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_073 :
    generatedNinthLowerSpinSourceQReplayWord 6 73 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 9).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 9)
    1752 24 0 (prefix_sizes 9) slice_073
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1752 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_074 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1776 1800 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 10 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_074 :
    generatedNinthLowerSpinSourceQReplayWord 6 74 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 10).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 10)
    1776 24 0 (prefix_sizes 10) slice_074
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1776 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_075 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1800 1824 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 11 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_075 :
    generatedNinthLowerSpinSourceQReplayWord 6 75 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 11).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 11)
    1800 24 0 (prefix_sizes 11) slice_075
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1800 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_076 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1824 1848 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 12 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_076 :
    generatedNinthLowerSpinSourceQReplayWord 6 76 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 12).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 12)
    1824 24 0 (prefix_sizes 12) slice_076
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1824 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_077 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1848 1872 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 13 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_077 :
    generatedNinthLowerSpinSourceQReplayWord 6 77 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 13).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 13)
    1848 24 0 (prefix_sizes 13) slice_077
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1848 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_078 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1872 1896 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 14 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_078 :
    generatedNinthLowerSpinSourceQReplayWord 6 78 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 14).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 14)
    1872 24 0 (prefix_sizes 14) slice_078
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1872 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_079 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1896 1920 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 15 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_079 :
    generatedNinthLowerSpinSourceQReplayWord 6 79 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 15).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 15)
    1896 24 0 (prefix_sizes 15) slice_079
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1896 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Normalize one complete original source slice by a single list drop and take.
private theorem slice_080 :
    generatedNinthLowerSpinSourceQReplayPrefixWords06.extract 1920 1944 =
      generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 16 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The entire literal prefix is the identical actual full source prefix. -/
theorem generatedNinth_lower_spin_literal_q_replay_prefix_06_part_04_080 :
    generatedNinthLowerSpinSourceQReplayWord 6 80 =
      (fun j : Fin 24 =>
        (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 16).getD j.val 0) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayPrefixWords06
    (generatedNinthLowerSpinLiteralQReplayPrefixes06Part04 16)
    1920 24 0 (prefix_sizes 16) slice_080
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords06.getD (1920 + j.val) 0 = _
  exact congrFun h j

set_option maxHeartbeats 8000000 in
-- Extract the identical original signed primitive chunk exactly once.
private theorem letter_slice :
    generatedNinthLowerSpinSourceQReplayLetterWords06.extract 64 80 =
      generatedNinthLowerSpinLiteralQReplayLetters06Part04 := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

/-- The complete small letter table is exactly the original actual source table. -/
theorem generatedNinth_lower_spin_literal_q_replay_letters_06_part_04 :
    (fun n : Fin 16 =>
      generatedNinthLowerSpinSourceQReplayLetter 6 ⟨64 + n.val, by omega⟩) =
      (fun n => generatedNinthLowerSpinLiteralQReplayLetters06Part04.getD n.val (11, false)) := by
  have h := generatedNinth_lower_spin_literal_q_replay_slice_function
    generatedNinthLowerSpinSourceQReplayLetterWords06
    generatedNinthLowerSpinLiteralQReplayLetters06Part04
    64 16 (11, false) letter_size letter_slice
  funext n
  change generatedNinthLowerSpinSourceQReplayLetterWords06.getD (64 + n.val) (11, false) = _
  exact congrFun h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
