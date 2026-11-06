/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentY
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentTri

/-! # The Twelfth axis as an identification vector

`twelfthSrcVec : IdentVec` represents the canonical Twelfth axis `generatedTwelfthAxis`
(family representative `10`), the forward triality image of the incoming vector
`rhoLocal generatedTwelfthLocal v₅` (`twelfthYVec`). It is the generic triality image
`twTriVec` of `twelfthYVec`: odd short terms unpacked from the packed incoming tensor, octad
blocks by the octad Fourier transform, the packed tensor block by `trialityTensorT` plus the
packed odd-short part; the matrix block and the pair terms are literal data checked by the kernel
against the triality formulas. `twelfthSrc_rep` binds it to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The unit vector `e_i` or the sum `e_i + e_j`, materialized. -/
def twUnitSum (i j : ℕ) : List ℚ := (List.range 24).map (fun t => if t = i ∨ t = j then 1 else 0)

/-- The literal matrix block of the Twelfth axis: `5/16 I` plus rank-one terms. -/
def twelfthSrcMat : MatRep :=
  ⟨5 / 16, [
    ((1 / 16 : ℚ), twUnitSum 0 2), ((-1 / 16 : ℚ), twUnitSum 0 3),
    ((1 / 16 : ℚ), twUnitSum 0 18), ((-1 / 16 : ℚ), twUnitSum 0 19),
    ((1 / 16 : ℚ), twUnitSum 1 2), ((1 / 16 : ℚ), twUnitSum 1 3), ((1 / 16 : ℚ), twUnitSum 1 18),
    ((1 / 16 : ℚ), twUnitSum 1 19), ((-1 / 16 : ℚ), twUnitSum 2 16),
    ((1 / 16 : ℚ), twUnitSum 2 17), ((1 / 16 : ℚ), twUnitSum 3 16),
    ((1 / 16 : ℚ), twUnitSum 3 17), ((1 / 16 : ℚ), twUnitSum 16 18),
    ((-1 / 16 : ℚ), twUnitSum 16 19), ((-1 / 16 : ℚ), twUnitSum 17 18),
    ((-1 / 16 : ℚ), twUnitSum 17 19), ((-1 / 4 : ℚ), twUnitSum 1 1),
    ((1 / 4 : ℚ), twUnitSum 19 19)]⟩

/-- The literal pair terms of the Twelfth axis (short scale `1 / 4096`). -/
def twelfthSrcPairs : List (ℕ × ℤ) := [
  (0, -256), (1, -256), (2, -256), (15, 256), (16, -256), (17, -256), (18, -256), (23, 256),
  (24, -256), (37, -256), (38, 256), (39, 256), (40, -256), (45, 256), (58, 256), (59, 256),
  (60, -256), (61, 256), (78, 256), (79, -256), (80, 256), (81, -256), (86, -256), (101, 256),
  (102, -256), (119, -256), (120, 256), (123, -256), (138, 256), (139, -256), (154, -256),
  (155, 256), (157, 256), (159, 256), (162, 256), (172, 256), (174, 256), (175, 256), (186, 256),
  (189, 256), (199, 256), (200, 256), (212, 256), (221, 256), (248, -256), (249, -256),
  (250, -256), (255, -256), (256, 256), (261, 256), (270, -256), (275, -256), (276, 256),
  (277, -256), (278, -256), (291, -256), (292, 256), (293, -256), (294, -256), (299, 256),
  (300, -256), (313, 256), (314, -256), (315, 256), (316, -256), (321, -256), (334, 256),
  (335, 256), (336, 256), (337, -256), (354, 256), (355, -256), (356, -256), (357, 256),
  (362, 256), (377, -256), (378, 256), (395, 256), (396, -256), (399, 256), (414, -256),
  (415, 256), (430, 256), (431, -256), (433, -256), (435, -256), (438, -256), (448, -256),
  (450, -256), (451, -256), (462, -256), (465, -256), (475, -256), (476, -256), (488, -256),
  (497, -256), (524, 256), (525, -256), (526, -256), (531, -256), (532, 256), (537, -256),
  (546, 256), (551, 256)]

/-- The octads of the incoming octad blocks, increasing. -/
def twelfthSrcOcts : List ℕ := [
  0, 3, 4, 5, 8, 9, 10, 11, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
  33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56,
  57, 58, 59, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 85, 86,
  89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 101, 102, 105, 106, 107, 108, 109, 110, 111, 112, 113,
  114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132,
  133, 134, 135, 136, 137, 142, 143, 144, 145, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
  160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 184,
  185, 190, 191, 192, 193, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209,
  216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 234, 235, 236, 237, 238,
  239, 240, 241, 244, 245, 246, 247, 248, 249, 251, 252, 253, 254, 255, 257, 258, 259, 260, 262,
  264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 285, 293, 296, 297, 298, 299, 300,
  301, 302, 303, 304, 305, 306, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328,
  329, 330, 331, 332, 333, 334, 335, 336, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356,
  357, 358, 359, 360, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 374, 375, 376, 377,
  378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 389, 390, 391, 392, 393, 394, 395, 396, 397,
  398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416,
  417, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 432, 433, 434, 435, 436, 437,
  438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456,
  457, 458, 459, 460, 461, 462, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476,
  477, 479, 480, 481, 482, 483, 484, 485, 486, 487, 489, 490, 491, 492, 493, 494, 495, 496, 497,
  498, 499, 500, 501, 502, 503, 504, 505, 508, 511, 512, 513, 514, 515, 516, 517, 518, 539, 540,
  541, 542, 543, 544, 545, 546, 551, 552, 553, 554, 555, 556, 557, 558, 563, 564, 571, 572, 573,
  574, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 595, 596, 599, 600,
  601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 615, 616, 617, 618, 619, 620, 621, 622, 625,
  626, 627, 628, 629, 630, 638, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653,
  654, 655, 656, 657, 658, 659, 660, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 683,
  693, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 714, 716, 717, 718, 719, 721,
  722, 723, 724, 725, 727, 728, 729, 731, 733, 734, 736, 737, 738, 739, 740, 742, 743, 745, 746,
  747, 748, 749, 751, 752, 754, 756, 757, 758]

/-- The image of the unit vector `e_0` under the spatial Twelfth source word. -/
def twelfthYV0 : List ℚ :=
  [(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ),
    (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_0` to `twelfthYV0`. -/
theorem twelfthYV0_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 0) = twelfthYV0 := by
  decide +kernel

/-- The image of the unit vector `e_1` under the spatial Twelfth source word. -/
def twelfthYV1 : List ℚ :=
  [(-1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ),
    (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_1` to `twelfthYV1`. -/
theorem twelfthYV1_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 1) = twelfthYV1 := by
  decide +kernel

/-- The image of the unit vector `e_2` under the spatial Twelfth source word. -/
def twelfthYV2 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ), (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_2` to `twelfthYV2`. -/
theorem twelfthYV2_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 2) = twelfthYV2 := by
  decide +kernel

/-- The image of the unit vector `e_3` under the spatial Twelfth source word. -/
def twelfthYV3 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_3` to `twelfthYV3`. -/
theorem twelfthYV3_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 3) = twelfthYV3 := by
  decide +kernel

/-- The image of the unit vector `e_16` under the spatial Twelfth source word. -/
def twelfthYV4 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_16` to `twelfthYV4`. -/
theorem twelfthYV4_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 16) = twelfthYV4 := by
  decide +kernel

/-- The image of the unit vector `e_17` under the spatial Twelfth source word. -/
def twelfthYV5 : List ℚ :=
  [(1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_17` to `twelfthYV5`. -/
theorem twelfthYV5_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 17) = twelfthYV5 := by
  decide +kernel

/-- The image of the unit vector `e_18` under the spatial Twelfth source word. -/
def twelfthYV6 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_18` to `twelfthYV6`. -/
theorem twelfthYV6_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 18) = twelfthYV6 := by
  decide +kernel

/-- The image of the unit vector `e_19` under the spatial Twelfth source word. -/
def twelfthYV7 : List ℚ :=
  [(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ),
    (1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial Twelfth source word maps `e_19` to `twelfthYV7`. -/
theorem twelfthYV7_spec :
    spWordVec identSpatialAlphabet twelfthYWord (unitList 19) = twelfthYV7 := by
  decide +kernel

/-- The literal matrix block of the incoming Twelfth vector. -/
def twelfthYMatLit : MatRep :=
  ⟨1 / 4, [(1 / 4, twelfthYV0), (1 / 4, twelfthYV1), (1 / 4, twelfthYV2), (1 / 4, twelfthYV3),
    (1 / 4, twelfthYV4), (1 / 4, twelfthYV5), (1 / 4, twelfthYV6), (1 / 4, twelfthYV7)]⟩

/-- The spatial image of the Fifth matrix block is the literal block. -/
theorem twelfthYMat_eq : fifthSrcMat.act identSpatialAlphabet twelfthYWord = twelfthYMatLit := by
  simp only [MatRep.act, fifthSrcMat, List.map_cons, List.map_nil]
  rw [twelfthYV0_spec, twelfthYV1_spec, twelfthYV2_spec, twelfthYV3_spec, twelfthYV4_spec,
    twelfthYV5_spec, twelfthYV6_spec, twelfthYV7_spec]
  rfl

/-- The denominator of the packed incoming tensor. -/
def twelfthYDen : ℚ := (tensorWordDenAll twelfthYWord : ℚ) * 1

/-- The incoming Twelfth vector with the literal matrix block. -/
def twelfthYLit : IdentVec :=
  ⟨twelfthYMatLit, ShortData.ofList twelfthYT, 1 / 16, tensorRat 128 twelfthYX twelfthYDen⟩

/-- The literal incoming representation is the incoming representation. -/
theorem twelfthYLit_eq : twelfthYVec = twelfthYLit := by
  unfold twelfthYVec twelfthYLit twelfthYDen
  rw [twelfthYMat_eq]

/-- The Twelfth axis as an identification vector. -/
def twelfthSrcVec : IdentVec :=
  twTriVec 128 twelfthYLit twelfthYX twelfthYDen twelfthSrcMat twelfthSrcPairs twelfthSrcOcts 32 256

/-- The packed tensor of the Twelfth representation. -/
def twelfthSrcX : List SVec := twTriTen 128 256 twelfthYX twelfthYLit.sh.odd

/-- The incoming tensor denominator is `2048`. -/
theorem twelfthYDen_eq : twelfthYDen = 2048 := by
  unfold twelfthYDen
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal matrix block agrees with the triality formula. -/
theorem twelfthSrc_mat : twMatCheck twelfthSrcMat twelfthYLit = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal pair terms agree with the triality formulas. -/
theorem twelfthSrc_pairs : twPairCheck twelfthSrcPairs twelfthYLit twelfthYDen = true := by
  rw [twelfthYDen_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad list covers the incoming octad blocks. -/
theorem twelfthSrc_octs : twOctCheck twelfthSrcOcts twelfthYLit = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem twelfthSrc_oddBound :
    twelfthYLit.sh.odd.all (fun q => decide ((256 * q.2).natAbs ≤ 1024)) = true ∧
      4 * (tensorWordGrowthAll twelfthYWord * 64) + twelfthYLit.sh.odd.length * 1024 < 2 ^ 128 := by
  decide +kernel

/-- The Twelfth axis is represented exactly. -/
theorem twelfthSrc_actual : griessConwayEncode generatedTwelfthAxis = twelfthSrcVec.real := by
  have hok : twelfthYLit.sh.ok = true := by rw [← twelfthYLit_eq]; exact twelfthYVec_ok
  have hx : griessConwayEncode (rhoLocal generatedTwelfthLocal generatedFifthAxis) =
      twelfthYLit.real := by rw [← twelfthYLit_eq]; exact twelfthY_actual
  have hsden : twelfthYLit.sden = 1 / 16 := rfl
  rw [generatedTwelfthAxis_local_expression]
  exact twTriVec_actual 128 _ 1024 twelfthYLit twelfthYX twelfthYDen twelfthSrcMat
    twelfthSrcPairs twelfthSrcOcts 32 256 hok rfl (by rw [twelfthYDen_eq]; norm_num)
    twelfthYX_bnd twelfthSrc_oddBound.1 twelfthSrc_oddBound.2
    (by rw [twelfthYDen_eq, hsden]; norm_num) (by rw [twelfthYDen_eq, hsden]; norm_num)
    twelfthSrc_mat twelfthSrc_pairs twelfthSrc_octs _ hx

/-- The representation of family representative `10`. -/
theorem twelfthSrc_rep : griessConwayEncode (generatedAxisGlobalTwelveRepresentative 10) =
    twelfthSrcVec.real := twelfthSrc_actual

/-- The short block of the Twelfth representation satisfies the range conditions. -/
theorem twelfthSrcVec_ok : twelfthSrcVec.sh.ok = true :=
  twTriVec_ok _ _ _ _ _ _ _ _ _ twelfthSrc_pairs twelfthSrc_octs

/-- The tensor block of the Twelfth representation. -/
theorem twelfthSrcVec_ten : twelfthSrcVec.ten = tensorRat 128 twelfthSrcX (2 * twelfthYDen) := rfl

/-- Bounds of the packed Twelfth tensor. -/
theorem twelfthSrcX_bnd :
    TBnd 128 (4 * (tensorWordGrowthAll twelfthYWord * 64) + twelfthYLit.sh.odd.length * 1024)
      twelfthSrcX :=
  twTriTen_bnd 128 _ 1024 256 twelfthYX twelfthYLit.sh.odd twelfthYX_bnd
    (fun q hq => by
      have h := twelfthSrc_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    twelfthSrc_oddBound.2

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
