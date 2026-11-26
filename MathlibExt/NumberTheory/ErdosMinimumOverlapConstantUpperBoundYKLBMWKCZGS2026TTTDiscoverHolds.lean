/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`results/mathematics/ttt_erdos_sequence.json` (test-time-training/discover),
at commit c9f51e47b653dc3359f33eb61aa291964890c958:
Copyright (c) 2025 Mert Yuksekgonul.
Licensed under the MIT License (https://opensource.org/licenses/MIT).
Authors: Yuksekgonul, Koceja, Li, Bianchi, McCaleb, Wang, Kautz, Choi, Zou, Guestrin, Sun.
Modifications: the heights are rounded to multiples of 1e-12, and entry 270 (0-based) is raised
by 6e-12 so that the integral is 1.
-/
module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! # TTT-Discover upper bound for minimum overlap

A rational step function and its finite correlation certificate give the upper bound
`380876 / 1000000` for the continuous Erdős minimum-overlap constant.

References: Mert Yuksekgonul et al., *Learning to Discover at Test Time* (2026),
arXiv:2601.16175; Terence Tao (curator), *Optimization Constants in Mathematics*, Constant 1b.
The latter source is frozen at commit `2c1968cd520b60f1cf3cf50749f7285e800e4e15`,
`constants/1b.md`, SHA-256
`1c51678108c90a2e841e1b49fa97940e4e1870324e1d949ddcb5b4345a0153ec`.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-- **TTT-Discover 2026 upper bound statement for the minimum overlap constant.** This is the
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ is at most $0.380876$.

Source: Yuksekgonul et al. 2026 (TTT-Discover); Optimization Problems, Constant 1b. -/
def upperBound_YKLBMWKCZGS2026_TTTDiscover : Prop := C₁ᵦ ≤ (380876 : ℝ) / 1000000

private def tttChunk00 : List Nat :=
  [0, 0, 1428, 766, 0,
    0, 5566, 0, 0, 0,
    0, 0, 0, 1882, 0,
    839, 106, 2634, 68, 0,
    2114501, 1600291, 0, 0, 0,
    1111, 0, 8754159, 9072630, 0]

private def tttChunk01 : List Nat :=
  [1230932, 58145259, 0, 244338, 0,
    0, 0, 3056695, 0, 7411890,
    23562626, 3072758, 15990722, 0, 186,
    7631445, 0, 1678123, 10343940, 6236443,
    0, 0, 11339507, 0, 44950461,
    37490468, 1857507, 79640426, 91408298, 100881765]

private def tttChunk02 : List Nat :=
  [1282222129, 8175412340, 8220042532, 13567290541, 3095970642,
    0, 5830057, 8231134, 16235900229, 104755679735,
    325390247080, 410151660619, 457356617099, 542669067356, 638920648472,
    702383606572, 716603121805, 634952265985, 589334511942, 565004478829,
    611821659197, 691670651092, 750757423054, 746488507036, 693437001765,
    686081198507, 757219779621, 825038648854, 876989264269, 887848609299]

private def tttChunk03 : List Nat :=
  [841450970000, 796450751722, 791184322169, 812622410073, 814009411200,
    845984501554, 892844306144, 942286566580, 963156108290, 988293693796,
    972970766021, 899926749000, 777194097100, 725333078440, 646020613134,
    565178174752, 475503264915, 305907271703, 124185902105, 43606405576,
    2077663910, 1039, 0, 10142114, 25235032,
    495, 40741250, 15278863, 0, 31197408]

private def tttChunk04 : List Nat :=
  [21870940, 35400783, 103265397, 94244746, 87898180,
    80014117, 88506506538, 183345275312, 238821171940, 365367882333,
    520863600941, 634270755269, 730599044656, 756556701926, 740844498682,
    719591517004, 702943651445, 726934381527, 745323648393, 751478426805,
    823795403955, 831602396735, 798691026370, 786765991044, 766833026792,
    716617306181, 661268563142, 598371946432, 551173989898, 466423149701]

private def tttChunk05 : List Nat :=
  [414445743855, 393020105518, 403353809467, 421225670179, 430137207624,
    442595691144, 469201060938, 437622073397, 410069851754, 379501129917,
    366537494131, 421653525124, 498777122671, 565094002523, 608485171324,
    633557917166, 656693917797, 712028426811, 773022876257, 834615531892,
    864097186659, 842130887399, 765217331708, 762819891278, 758377114902,
    766661668061, 791307592253, 786452785514, 768910382877, 800411715349]

private def tttChunk06 : List Nat :=
  [762910731669, 701250279098, 582072369607, 467958226025, 415897838596,
    388022634317, 346202014611, 305579428340, 257170365063, 205659688968,
    160321465281, 160011554252, 193219785096, 215064111552, 263152423723,
    334804725779, 448029450023, 541247008324, 586444898659, 641500096664,
    704342357616, 752466622566, 788828931498, 777260430377, 791965884845,
    809555070983, 807653815332, 794859344838, 748803011604, 664029059672]

private def tttChunk07 : List Nat :=
  [618031951101, 567353152373, 549151759542, 563956946117, 582017499678,
    651832742788, 713596794554, 736239118680, 740396487206, 691678324692,
    626968548106, 594526853498, 605849432943, 621394798876, 668973850050,
    744317268645, 835117952409, 911408607888, 951091891065, 999963143749,
    999947055091, 999982446531, 997270567203, 958310873844, 879291832790,
    860741850394, 801498811474, 693421018739, 636728315588, 606431650111]

private def tttChunk08 : List Nat :=
  [574741947720, 548255453652, 529702678768, 559557500018, 548567266632,
    508646951240, 519364464641, 539337738334, 605847394262, 851295260237,
    929518958496, 970120478574, 985441879631, 991857838188, 987292269474,
    997806818272, 966998384870, 914269999023, 881856316611, 892756339853,
    771883747223, 621192345383, 618169784648, 478943896175, 522736824426,
    672166437116, 822218805472, 946076698330, 999997267505, 999992958224]

private def tttChunk09 : List Nat :=
  [999968457962, 999997345280, 999939945208, 999980916886, 999998544126,
    999996711564, 999998168965, 999950113045, 999984931083, 908639729154,
    951452533464, 955762604536, 920986069772, 802153553270, 684561625486,
    795623770629, 816114313729, 844398365250, 911542439417, 934814142924,
    993021325965, 999946024661, 999999729118, 999998115624, 999928486114,
    999953442745, 999933008309, 999998175869, 980887730979, 948378676567]

private def tttChunk10 : List Nat :=
  [965519899222, 957772145121, 999958949389, 999930438775, 999930180858,
    999961576727, 999998945383, 999892557999, 985014358523, 943538942489,
    999945254345, 999970638260, 999953243962, 999925996832, 999948520360,
    999989455563, 970593346689, 935733212718, 889942706191, 939653463150,
    939323512784, 891203420141, 791462873129, 772534593774, 717194409743,
    807913083333, 756528809617, 828169206501, 925321438496, 845346254798]

private def tttChunk11 : List Nat :=
  [697660827075, 675042507824, 698976271852, 667161258123, 746552968668,
    908935408648, 999996593934, 999975513731, 999924264050, 999993904178,
    993250381489, 969150069079, 977245444043, 950631400252, 917441369332,
    949617076657, 994202640717, 999999541342, 995293433633, 893089251674,
    739019721415, 617248614132, 555943015736, 512815349615, 508737606095,
    548443769463, 556297399921, 532955814778, 548359560792, 574815383135]

private def tttChunk12 : List Nat :=
  [606517449228, 655711067622, 721547250344, 770870677992, 831007299271,
    902549330259, 952436596331, 993092468461, 983027115358, 993657651106,
    995430730956, 927166059787, 900866299879, 855582828746, 735677874176,
    691701428533, 649554408707, 606042757858, 594612246398, 623868530981,
    695040411354, 740576482111, 736304343806, 713669817439, 651853017573,
    584052901653, 561970923471, 549209689395, 567372472125, 618071357341]

private def tttChunk13 : List Nat :=
  [664049749421, 748810053217, 794839706521, 807632069845, 809581141905,
    791976086514, 777280831033, 788853003642, 752525969592, 704355769872,
    641452941618, 586487650591, 541182220891, 447989378504, 334733688742,
    263139694003, 215057084776, 193218177821, 160039902894, 160289141810,
    205550469198, 257207966796, 305599753948, 346239897234, 388040839630,
    415925796480, 467931256579, 582056385491, 701439859737, 762922970506]

private def tttChunk14 : List Nat :=
  [800373783677, 768904849898, 786467212696, 791253550117, 766686378180,
    758343968393, 762666638837, 765152516463, 842222738060, 864178838218,
    834558956472, 773021218180, 712030189185, 656730441157, 633576451901,
    608509087337, 565088087753, 498731051898, 421680561381, 366503559938,
    379485798840, 410087385066, 437530972475, 469075970202, 442650343110,
    430228049328, 421291760035, 403332637300, 392922076134, 414447347817]

private def tttChunk15 : List Nat :=
  [466423710009, 551125199214, 598428143681, 661488121903, 716570262042,
    766799826251, 786699163118, 798744667591, 831549552957, 823731065917,
    751442891896, 745276833558, 726921864266, 702983581842, 719651285766,
    740941578457, 756584357795, 730554436447, 634345523672, 520931741088,
    365447666920, 238879774843, 183405511686, 88437039543, 55198128,
    27692944, 2571991, 18918720, 41618331, 12724803]

private def tttChunk16 : List Nat :=
  [0, 0, 1514062, 34571758, 9352673,
    78491122, 112488085, 29256420, 20778914, 2142845598,
    43599309920, 124229728218, 305847909017, 475432261699, 565151968018,
    645910399012, 725275124980, 777245213512, 899986856453, 972962197234,
    988321957302, 963078669232, 942234857130, 892912531141, 845964997540,
    814024351643, 812570887302, 791154063643, 796516540962, 841444037492]

private def tttChunk17 : List Nat :=
  [887849793015, 876981087051, 825097917195, 757282722400, 686183774650,
    693385756521, 746550789331, 750715579965, 691650569555, 611787292947,
    564995151462, 589212574910, 634915288103, 716720246909, 702322723349,
    638902538656, 542702040233, 457379835656, 410166434343, 325325839271,
    104671788576, 16203058630, 887, 128171299, 34656802,
    3057997905, 13637351734, 8252222433, 8203389448, 1252985807]

private def tttChunk18 : List Nat :=
  [35387586, 17624382, 18234995, 8596569, 2266,
    97876, 46237752, 52986342, 69116943, 4911670,
    25891721, 28, 631998, 0, 544,
    36270251, 0, 0, 29811339, 0,
    36031663, 134, 62507523, 3740, 251,
    308, 0, 0, 0, 0]

private def tttChunk19 : List Nat :=
  [0, 0, 4898, 0, 3426,
    0, 791, 0, 0, 371,
    0, 0, 0, 0, 0,
    0, 0, 0, 0, 0,
    0, 0, 0, 0, 0,
    0, 0, 732, 0, 0]

private def tttNumers : List Nat :=
  tttChunk00 ++ tttChunk01 ++ tttChunk02 ++ tttChunk03 ++ tttChunk04 ++
  tttChunk05 ++ tttChunk06 ++ tttChunk07 ++ tttChunk08 ++ tttChunk09 ++
  tttChunk10 ++ tttChunk11 ++ tttChunk12 ++ tttChunk13 ++ tttChunk14 ++
  tttChunk15 ++ tttChunk16 ++ tttChunk17 ++ tttChunk18 ++ tttChunk19

private def tttDot (a b : List Nat) : Nat :=
  (a.zipWith (fun x y => x * (1000000000000 - y)) b).sum

private theorem tttNumers_length : tttNumers.length = 600 := by decide +kernel
private theorem tttNumers_sum : tttNumers.sum = 300000000000000 := by decide +kernel
private theorem tttNumers_all : (tttNumers.all fun x => decide (x ≤ 1000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock00 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (0 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (0 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock01 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (30 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (30 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock02 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (60 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (60 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock03 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (90 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (90 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock04 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (120 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (120 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock05 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (150 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (150 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock06 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (180 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (180 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock07 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (210 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (210 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock08 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (240 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (240 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock09 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (270 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (270 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock10 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (300 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (300 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock11 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (330 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (330 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock12 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (360 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (360 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock13 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (390 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (390 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock14 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (420 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (420 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock15 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (450 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (450 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock16 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (480 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (480 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock17 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (510 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (510 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock18 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (540 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (540 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private theorem tttCorrBlock19 :
    ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (570 + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (570 + i)) tttNumers ≤ 114262800000000000000000000)) = true := by
  decide +kernel

private noncomputable def cell (i : ℤ) : Set ℝ :=
  Ico ((i : ℝ) / 300 - 1) (((i : ℝ) + 1) / 300 - 1)
private theorem cell_overlap (i j k : ℤ) (x u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hx : 300 * x = (k : ℝ) + u) :
    volume.real (cell i ∩ (fun t : ℝ => x + t) ⁻¹' cell j) =
      (if j - i = k then (1 - u) / 300 else 0) +
      (if j - i = k + 1 then u / 300 else 0) := by
  have hs : cell i ∩ (fun t : ℝ => x + t) ⁻¹' cell j =
      Ico (max ((i : ℝ) / 300 - 1) ((j : ℝ) / 300 - 1 - x))
        (min (((i : ℝ) + 1) / 300 - 1) (((j : ℝ) + 1) / 300 - 1 - x)) := by
    ext t
    simp only [cell, mem_inter_iff, mem_preimage, mem_Ico, max_le_iff, lt_min_iff]
    constructor <;> intro h <;> constructor <;> constructor <;>
      linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  rw [hs, Real.volume_real_Ico]
  by_cases h0 : j - i = k
  · have he : (j : ℝ) - i = k := by exact_mod_cast h0
    have h1 : j - i ≠ k + 1 := by omega
    rw [ite_eq_left h0, ite_eq_right h1, add_zero]
    rw [max_eq_left (a := (i : ℝ) / 300 - 1) (b := (j : ℝ) / 300 - 1 - x) (by linarith),
      min_eq_right (by linarith), max_eq_left (by linarith)]
    linarith
  · by_cases h1 : j - i = k + 1
    · have he : (j : ℝ) - i = (k : ℝ) + 1 := by exact_mod_cast h1
      rw [ite_eq_right h0, ite_eq_left h1, zero_add]
      rw [max_eq_right (a := (i : ℝ) / 300 - 1) (b := (j : ℝ) / 300 - 1 - x) (by linarith),
        min_eq_left (by linarith), max_eq_left (by linarith)]
      linarith
    · rw [ite_eq_right h0, ite_eq_right h1, add_zero]
      apply max_eq_right
      rcases lt_or_gt_of_ne h0 with hl | hr
      · have hl' : j - i ≤ k - 1 := by omega
        have he : (j : ℝ) - i ≤ (k : ℝ) - 1 := by exact_mod_cast hl'
        exact le_trans (sub_le_sub (min_le_right _ _) (le_max_left _ _)) (by linarith)
      · have hr' : k + 2 ≤ j - i := by omega
        have he : (k : ℝ) + 2 ≤ (j : ℝ) - i := by exact_mod_cast hr'
        exact le_trans (sub_le_sub (min_le_left _ _) (le_max_right _ _)) (by linarith)
private noncomputable def step (h : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 600, (cell i).indicator (fun _ => h i) t
private theorem cell_unique {i j : ℕ} {t : ℝ} (hi : t ∈ cell i) (hj : t ∈ cell j) : i = j := by
  change (i : ℝ) / 300 - 1 ≤ t ∧ t < ((i : ℝ) + 1) / 300 - 1 at hi
  change (j : ℝ) / 300 - 1 ≤ t ∧ t < ((j : ℝ) + 1) / 300 - 1 at hj
  have h1 : (i : ℝ) < j + 1 := by linarith
  have h2 : (j : ℝ) < i + 1 := by linarith
  have h1' : i < j + 1 := by exact_mod_cast h1
  have h2' : j < i + 1 := by exact_mod_cast h2
  omega
private theorem step_on_cell (h : ℕ → ℝ) (j : ℕ) (hj : j < 600) {t : ℝ}
    (ht : t ∈ cell j) : step h t = h j := by
  unfold step
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem ht _
  · intro i _ hij
    exact indicator_of_notMem (fun hi => hij (cell_unique hi ht)) _
  · exact fun hnot => (hnot (Finset.mem_range.mpr hj)).elim
private theorem cell_subset (i : ℕ) (hi : i < 600) : cell i ⊆ Ico (-1 : ℝ) 1 := by
  intro t ht
  change (i : ℝ) / 300 - 1 ≤ t ∧ t < ((i : ℝ) + 1) / 300 - 1 at ht
  have hi' : (i : ℝ) + 1 ≤ 600 := by exact_mod_cast (show i + 1 ≤ 600 by omega)
  exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) i], by linarith⟩
private theorem cell_exists (t : ℝ) (ht : t ∈ Ico (-1 : ℝ) 1) :
    ∃ i : ℕ, i < 600 ∧ t ∈ cell i := by
  let k : ℤ := ⌊300 * (t + 1)⌋
  have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (by linarith [ht.1])
  have hk : (k : ℝ) ≤ 300 * (t + 1) := Int.floor_le _
  have hk1 : 300 * (t + 1) < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hk600 : k < 600 := by
    have : (k : ℝ) < 600 := by linarith [ht.2]
    exact_mod_cast this
  refine ⟨k.toNat, by omega, ?_⟩
  change (k.toNat : ℝ) / 300 - 1 ≤ t ∧ t < ((k.toNat : ℝ) + 1) / 300 - 1
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
  rw [hcast]
  constructor <;> linarith
private theorem step_outside (h : ℕ → ℝ) (t : ℝ) (ht : t ∉ Ico (-1 : ℝ) 1) :
    step h t = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact indicator_of_notMem (fun hit => ht (cell_subset i (Finset.mem_range.mp hi) hit)) _
private theorem step_measurable (h : ℕ → ℝ) : Measurable (step h) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator measurableSet_Ico)
private theorem step_range (h : ℕ → ℝ) (hh : ∀ i < 600, h i ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    step h t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ico (-1 : ℝ) 1
  · obtain ⟨i, hi, hit⟩ := cell_exists t ht
    rw [step_on_cell h i hi hit]
    exact hh i hi
  · rw [step_outside h t ht]
    exact ⟨le_rfl, zero_le_one⟩
private theorem step_integral (h : ℕ → ℝ) :
    (∫ t, step h t) = (∑ i ∈ Finset.range 600, h i) / 300 := by
  unfold step
  rw [integral_finsetSum]
  · simp only [integral_indicator measurableSet_Ico, cell, integral_const,
      measureReal_restrict_apply_univ, Real.volume_real_Ico, Int.cast_natCast, smul_eq_mul]
    have hc (i : ℕ) : max ((((i : ℝ) + 1) / 300 - 1) - ((i : ℝ) / 300 - 1)) 0 = 1 / 300 := by
      rw [show (((i : ℝ) + 1) / 300 - 1) - ((i : ℝ) / 300 - 1) = 1 / 300 by ring]
      norm_num
    simp only [hc]
    rw [← Finset.mul_sum]
    ring
  · intro i _
    exact (integrableOn_const (μ := volume) (s := cell i)
      (measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico
private noncomputable def pairCell (i j : ℕ) (x : ℝ) : Set ℝ :=
  cell i ∩ (fun t : ℝ => x + t) ⁻¹' cell j
private theorem pairCell_eq (i j : ℕ) (x : ℝ) :
    pairCell i j x =
      Ico (max ((i : ℝ) / 300 - 1) ((j : ℝ) / 300 - 1 - x))
        (min (((i : ℝ) + 1) / 300 - 1) (((j : ℝ) + 1) / 300 - 1 - x)) := by
  ext t
  simp only [pairCell, cell, Int.cast_natCast, mem_inter_iff, mem_preimage, mem_Ico,
    max_le_iff, lt_min_iff]
  constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
private theorem pairCell_integrable (i j : ℕ) (x c : ℝ) :
    Integrable ((pairCell i j x).indicator fun _ => c) := by
  rw [pairCell_eq]
  exact (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico
private theorem step_product (h v : ℕ → ℝ) (x t : ℝ) :
    step h t * step v (x + t) =
      ∑ i ∈ Finset.range 600, ∑ j ∈ Finset.range 600,
        (pairCell i j x).indicator (fun _ => h i * v j) t := by
  unfold step
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : t ∈ cell i <;> by_cases hj : x + t ∈ cell j <;>
    simp [pairCell, hi, hj]
private noncomputable def corr (h v : ℕ → ℝ) (k : ℤ) : ℝ :=
  ∑ i ∈ Finset.range 600, ∑ j ∈ Finset.range 600,
    if (j : ℤ) - i = k then h i * v j else 0
private theorem pairCell_integral (i j : ℕ) (x c : ℝ) :
    (∫ t, (pairCell i j x).indicator (fun _ => c) t) = volume.real (pairCell i j x) * c := by
  rw [integral_indicator (by rw [pairCell_eq]; exact measurableSet_Ico), integral_const]
  simp [smul_eq_mul]
private theorem step_overlap (h v : ℕ → ℝ) (k : ℤ) (x u : ℝ)
    (hu : 0 ≤ u) (hu1 : u < 1) (hx : 300 * x = (k : ℝ) + u) :
    (∫ t, step h t * step v (x + t)) =
      (1 - u) / 300 * corr h v k + u / 300 * corr h v (k + 1) := by
  simp_rw [step_product]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => pairCell_integrable i j x (h i * v j)))]
  simp_rw [integral_finsetSum _ (fun j _ => pairCell_integrable _ j x _)]
  simp_rw [pairCell_integral]
  simp_rw [show ∀ i j : ℕ, volume.real (pairCell i j x) =
      (if (j : ℤ) - i = k then (1 - u) / 300 else 0) +
      (if (j : ℤ) - i = k + 1 then u / 300 else 0) from
    fun i j => cell_overlap i j k x u hu hu1 hx]
  have hf (p : Prop) [Decidable p] (a b : ℝ) :
      (if p then a else 0) * b = a * (if p then b else 0) := by
    split_ifs <;> ring
  simp_rw [add_mul, hf, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

private theorem list_sum (a : List Nat) :
    (∑ i ∈ Finset.range a.length, a.getD i 0) = a.sum := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, List.sum_cons, ih, Nat.add_comm]
private theorem dot_sum (a b : List Nat) :
    tttDot a b = ∑ i ∈ Finset.range a.length,
      if i < b.length then a.getD i 0 * (1000000000000 - b.getD i 0) else 0 := by
  induction a generalizing b with
  | nil => simp [tttDot]
  | cons x xs ih =>
    cases b with
    | nil => simp [tttDot]
    | cons y ys =>
      simp only [tttDot, List.zipWith_cons_cons, List.sum_cons, List.length_cons,
        Finset.sum_range_succ']
      rw [show (List.zipWith (fun x y => x * (1000000000000 - y)) xs ys).sum =
        tttDot xs ys from rfl,
        ih]
      simp [Nat.add_comm]

private theorem tttNumer_le (i : ℕ) : tttNumers.getD i 0 ≤ 1000000000000 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : tttNumers[i]? with
  | none => simp
  | some a =>
    obtain ⟨h, he⟩ := List.getElem?_eq_some_iff.mp hi
    have ha := List.all_eq_true.mp tttNumers_all a (List.mem_iff_getElem.mpr ⟨i, h, he⟩)
    exact of_decide_eq_true ha
private noncomputable def tttHeightFun (i : ℕ) : ℝ :=
  (tttNumers.getD i 0 : ℝ) / 1000000000000
private noncomputable def tttF : ℝ → ℝ := step tttHeightFun
private noncomputable def tttG : ℝ → ℝ :=
  continuousSupportInterval.indicator (fun t => 1 - tttF t)
private theorem tttHeight_range (i : ℕ) : tttHeightFun i ∈ Icc (0 : ℝ) 1 := by
  have hi : (tttNumers.getD i 0 : ℝ) ≤ 1000000000000 := by exact_mod_cast tttNumer_le i
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  · dsimp [tttHeightFun]
    linarith
private theorem tttF_range (t : ℝ) : tttF t ∈ Icc (0 : ℝ) 1 :=
  step_range _ (fun i _ => tttHeight_range i) t
private theorem tttG_range (t : ℝ) : tttG t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ continuousSupportInterval
  · simp only [tttG, indicator_of_mem ht, mem_Icc]
    constructor <;> linarith [(tttF_range t).1, (tttF_range t).2]
  · simp [tttG, ht]
private theorem tttF_zero_outside (t : ℝ) (ht : t ∉ continuousSupportInterval) : tttF t = 0 :=
  step_outside _ t (fun h => ht ⟨h.1, h.2.le⟩)
private theorem tttF_integral : (∫ t : ℝ, tttF t) = 1 := by
  rw [tttF, step_integral]
  unfold tttHeightFun
  rw [← Finset.sum_div, ← Nat.cast_sum]
  rw [← tttNumers_length, list_sum, tttNumers_sum]
  norm_num
private theorem tttAdmissible : ContinuousAdmissible tttF tttG := by
  refine ⟨(step_measurable _).aemeasurable,
    (measurable_const.sub (step_measurable _)).indicator measurableSet_Icc |>.aemeasurable,
    tttF_range, tttG_range, tttF_zero_outside, ?_, ?_, tttF_integral⟩
  · intro t ht
    exact indicator_of_notMem ht _
  · intro t ht
    simp [tttG, ht]
private theorem tttG_eq_step (t : ℝ) (ht : t ≠ 1) :
    tttG t = step (fun i => 1 - tttHeightFun i) t := by
  by_cases hs : t ∈ Ico (-1 : ℝ) 1
  · obtain ⟨i, hi, hit⟩ := cell_exists t hs
    have hcc : t ∈ continuousSupportInterval := ⟨hs.1, hs.2.le⟩
    simp only [tttG, indicator_of_mem hcc, tttF, step_on_cell _ i hi hit]
  · rw [step_outside _ t hs]
    have hcc : t ∉ continuousSupportInterval := by
      intro h
      exact hs ⟨h.1, lt_of_le_of_ne h.2 ht⟩
    exact indicator_of_notMem hcc _
private theorem corr_nonneg_formula (k : ℕ) :
    corr tttHeightFun (fun i => 1 - tttHeightFun i) k =
      (tttDot tttNumers (tttNumers.drop k) : ℝ) / 1000000000000000000000000 := by
  rw [dot_sum, tttNumers_length]
  simp only [Nat.cast_sum]
  unfold corr
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hik : i + k < 600
  · rw [Finset.sum_eq_single (i + k)]
    · have hl : i < (tttNumers.drop k).length := by simp [tttNumers_length]; omega
      rw [ite_eq_left hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm k i]
      have hki : ((i + k : ℕ) : ℤ) - i = k := by omega
      rw [ite_eq_left hki, Nat.cast_mul]
      have hsub : tttNumers[i + k]?.getD 0 ≤ 1000000000000 := by
        simpa only [List.getD_eq_getElem?_getD] using tttNumer_le (i + k)
      rw [Nat.cast_sub hsub]
      unfold tttHeightFun
      simp only [List.getD_eq_getElem?_getD]
      push_cast
      ring
    · intro j _ hji
      apply ite_eq_right
      omega
    · exact fun h => (h (Finset.mem_range.mpr hik)).elim
  · have hl : ¬i < (tttNumers.drop k).length := by simp [tttNumers_length]; omega
    rw [ite_eq_right hl, Nat.cast_zero, zero_div]
    apply Finset.sum_eq_zero
    intro j hj
    apply ite_eq_right
    have hj' := Finset.mem_range.mp hj
    omega
private theorem corr_neg_formula (k : ℕ) :
    corr tttHeightFun (fun i => 1 - tttHeightFun i) (-(k : ℤ)) =
      (tttDot (tttNumers.drop k) tttNumers : ℝ) / 1000000000000000000000000 := by
  unfold corr
  rw [Finset.sum_comm]
  rw [dot_sum]
  have hlen : (tttNumers.drop k).length = 600 - k := by simp [tttNumers_length]
  rw [hlen]
  have hs :
      (∑ j ∈ Finset.range 600, ∑ i ∈ Finset.range 600,
        if (j : ℤ) - i = -(k : ℤ) then tttHeightFun i * (1 - tttHeightFun j) else 0) =
      ∑ j ∈ Finset.range (600 - k), tttHeightFun (j + k) * (1 - tttHeightFun j) := by
    symm
    calc
      _ = ∑ j ∈ Finset.range (600 - k), ∑ i ∈ Finset.range 600,
          if (j : ℤ) - i = -(k : ℤ) then tttHeightFun i * (1 - tttHeightFun j) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j + k < 600 := by have := Finset.mem_range.mp hj; omega
        rw [Finset.sum_eq_single (j + k)]
        · rw [ite_eq_left (by omega)]
        · intro i _ hij
          apply ite_eq_right
          omega
        · exact fun h => (h (Finset.mem_range.mpr hjk)).elim
      _ = _ := by
        apply Finset.sum_subset
        · intro j hj
          apply Finset.mem_range.mpr
          have := Finset.mem_range.mp hj
          omega
        · intro j hj hjnot
          have hj' := Finset.mem_range.mp hj
          have hjnot' : 600 - k ≤ j := by simpa using hjnot
          apply Finset.sum_eq_zero
          intro i hi
          apply ite_eq_right
          have hi' := Finset.mem_range.mp hi
          omega
  rw [hs, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj600 : j < tttNumers.length := by
    rw [tttNumers_length]
    have := Finset.mem_range.mp hj
    omega
  rw [ite_eq_left hj600, Nat.cast_mul, Nat.cast_sub (tttNumer_le j)]
  unfold tttHeightFun
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm k j]
  push_cast
  ring

private theorem tttCorr_le (k : ℕ) (hk : k < 600) :
    tttDot tttNumers (tttNumers.drop k) ≤ 114262800000000000000000000 ∧
    tttDot (tttNumers.drop k) tttNumers ≤ 114262800000000000000000000 := by
  have hq : k / 30 < 20 := by omega
  have hb : ((List.range 30).all fun i => decide
      (tttDot tttNumers (tttNumers.drop (30 * (k / 30) + i)) ≤ 114262800000000000000000000 ∧
       tttDot (tttNumers.drop (30 * (k / 30) + i)) tttNumers ≤
         114262800000000000000000000)) = true := by
    interval_cases he : k / 30
    · exact tttCorrBlock00
    · exact tttCorrBlock01
    · exact tttCorrBlock02
    · exact tttCorrBlock03
    · exact tttCorrBlock04
    · exact tttCorrBlock05
    · exact tttCorrBlock06
    · exact tttCorrBlock07
    · exact tttCorrBlock08
    · exact tttCorrBlock09
    · exact tttCorrBlock10
    · exact tttCorrBlock11
    · exact tttCorrBlock12
    · exact tttCorrBlock13
    · exact tttCorrBlock14
    · exact tttCorrBlock15
    · exact tttCorrBlock16
    · exact tttCorrBlock17
    · exact tttCorrBlock18
    · exact tttCorrBlock19
  have hr : k % 30 < 30 := Nat.mod_lt _ (by norm_num)
  have h := of_decide_eq_true (List.all_eq_true.mp hb (k % 30) (List.mem_range.mpr hr))
  have he : 30 * (k / 30) + k % 30 = k := by omega
  simpa only [he] using h
private theorem corr_bound (k : ℤ) :
    corr tttHeightFun (fun i => 1 - tttHeightFun i) k ≤ (1142628 : ℝ) / 10000 := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [corr_nonneg_formula]
    by_cases hn : n < 600
    · have hb : (tttDot tttNumers (tttNumers.drop n) : ℝ) ≤ 114262800000000000000000000 := by
        exact_mod_cast (tttCorr_le n hn).1
      linarith
    · have he : tttNumers.drop n = [] := List.drop_eq_nil_iff.mpr (by rw [tttNumers_length]; omega)
      norm_num [he, tttDot]
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -k by omega)
    have he : k = -(n : ℤ) := by omega
    rw [he, corr_neg_formula]
    by_cases hn : n < 600
    · have hb : (tttDot (tttNumers.drop n) tttNumers : ℝ) ≤ 114262800000000000000000000 := by
        exact_mod_cast (tttCorr_le n hn).2
      linarith
    · have he : tttNumers.drop n = [] := List.drop_eq_nil_iff.mpr (by rw [tttNumers_length]; omega)
      norm_num [he, tttDot]
private theorem tttOverlap_le (x : ℝ) (_ : x ∈ continuousTranslationInterval) :
    continuousOverlap tttF tttG x ≤ (380876 : ℝ) / 1000000 := by
  have hxt : ∀ᵐ t : ℝ, tttG (x + t) =
      step (fun i => 1 - tttHeightFun i) (x + t) := by
    filter_upwards [volume.ae_ne (1 - x)] with t ht
    apply tttG_eq_step
    intro he
    apply ht
    linarith
  have ho : continuousOverlap tttF tttG x =
      ∫ t, step tttHeightFun t * step (fun i => 1 - tttHeightFun i) (x + t) := by
    unfold continuousOverlap
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by simp [continuousOverlapIntegrand, tttF_zero_outside t ht])]
    apply integral_congr_ae
    filter_upwards [hxt] with t ht
    dsimp only [continuousOverlapIntegrand, tttF]
    exact congrArg (fun a : ℝ => step tttHeightFun t * a) ht
  rw [ho]
  let k : ℤ := ⌊300 * x⌋
  let u : ℝ := 300 * x - (k : ℝ)
  have hu : 0 ≤ u := sub_nonneg.mpr (Int.floor_le _)
  have hu1 : u < 1 := Int.fract_lt_one _
  rw [step_overlap _ _ k x u hu hu1 (by dsimp [u]; ring)]
  have h0 := mul_le_mul_of_nonneg_left (corr_bound k)
    (show 0 ≤ (1 - u) / 300 by exact div_nonneg (by linarith) (by norm_num))
  have h1 := mul_le_mul_of_nonneg_left (corr_bound (k + 1)) (show 0 ≤ u / 300 by positivity)
  linarith
private theorem tttPairScore_le :
    continuousPairScore tttF tttG ≤ (380876 : ℝ) / 1000000 := by
  apply csSup_le (continuousOverlapValues_nonempty tttF tttG)
  rintro y ⟨x, hx, rfl⟩
  exact tttOverlap_le x hx

/-- **TTT-Discover 2026 upper bound for the minimum overlap constant holds.** The continuous
Erdős minimum-overlap constant $C_{1b}$ is at most $0.380876$.

Source: Yuksekgonul et al. 2026 and Optimization Problems 1b. -/
public theorem upperBound_YKLBMWKCZGS2026_TTTDiscover_holds :
    upperBound_YKLBMWKCZGS2026_TTTDiscover :=
  (continuousMinimumOverlapConstant_isUniversalLowerBound tttF tttG tttAdmissible).trans
    tttPairScore_le

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
