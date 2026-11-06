/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthL
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcChecks

/-! # The Tenth axis as an identification vector

`tenthSrcVec : IdentVec` represents the canonical Tenth axis `generatedTenthAxis` (family
representative `11`), the forward triality image of the incoming vector `srcTenthYL` (=
`srcTenthYVec`). It is the generic triality image `twTriVec` (worker gtwelfth) of the incoming
vector: odd short terms unpacked from the packed incoming tensor, octad blocks by the octad Fourier
transform, the packed tensor block by `trialityTensorT` plus the packed odd-short part; the matrix
block and the pair terms are literal data checked by the kernel against the triality formulas (the
pair check in eight blocks). `tenthSrc_rep` binds it to the genuine coordinates.
Density: 312 pair terms, 22346 octad terms in 634 octads, 23424 odd terms, 48768 tensor entries;
short scale `1 / 33554432`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The unit vector `e_i` or the sum `e_i + e_j`, materialized. -/
def srcTenthUnit (i j : ℕ) : List ℚ :=
  (List.range 24).map (fun t => if t = i ∨ t = j then 1 else 0)

/-- The literal matrix block of the Tenth axis: a multiple of the identity plus rank-one terms. -/
def srcTenthMat : MatRep :=
  ⟨(9 / 32 : ℚ), [
    ((1 / 16 : ℚ), srcTenthUnit 0 3), ((1 / 16 : ℚ), srcTenthUnit 4 7),
    ((1 / 16 : ℚ), srcTenthUnit 4 13), ((-1 / 16 : ℚ), srcTenthUnit 4 14),
    ((-1 / 16 : ℚ), srcTenthUnit 4 17), ((1 / 16 : ℚ), srcTenthUnit 4 23),
    ((1 / 16 : ℚ), srcTenthUnit 5 6), ((1 / 16 : ℚ), srcTenthUnit 7 13),
    ((-1 / 16 : ℚ), srcTenthUnit 7 14), ((-1 / 16 : ℚ), srcTenthUnit 7 17),
    ((1 / 16 : ℚ), srcTenthUnit 7 23), ((1 / 16 : ℚ), srcTenthUnit 9 10),
    ((1 / 16 : ℚ), srcTenthUnit 12 15), ((-1 / 16 : ℚ), srcTenthUnit 13 14),
    ((-1 / 16 : ℚ), srcTenthUnit 13 17), ((1 / 16 : ℚ), srcTenthUnit 13 23),
    ((1 / 16 : ℚ), srcTenthUnit 14 17), ((-1 / 16 : ℚ), srcTenthUnit 14 23),
    ((1 / 16 : ℚ), srcTenthUnit 18 20), ((1 / 16 : ℚ), srcTenthUnit 19 22),
    ((1 / 4 : ℚ), srcTenthUnit 14 14), ((1 / 4 : ℚ), srcTenthUnit 17 17)]⟩

/-- The literal pair terms of the Tenth axis (short scale `1 / 33554432`). -/
def srcTenthPairs : List (ℕ × ℤ) := [
  (2, 1048576), (3, -1048576), (4, -1048576), (5, 1048576), (6, -1048576), (8, 1048576),
  (9, 1048576), (11, 1048576), (12, -1048576), (13, -1048576), (14, -1048576), (17, -1048576),
  (18, 1048576), (19, 1048576), (21, -1048576), (23, -1048576), (29, 1048576), (32, -1048576),
  (37, -1048576), (38, -1048576), (42, -1048576), (44, -1048576), (50, -1048576), (53, 1048576),
  (58, 1048576), (59, 1048576), (63, 1048576), (65, 1048576), (66, -1048576), (67, 1048576),
  (68, -1048576), (69, -1048576), (71, 1048576), (72, 1048576), (74, -1048576), (75, -1048576),
  (76, -1048576), (77, 1048576), (80, 1048576), (81, -1048576), (82, -1048576), (84, 1048576),
  (86, 1048576), (87, 1048576), (88, -1048576), (90, -1048576), (91, -1048576), (93, -1048576),
  (94, -1048576), (95, -3145728), (96, -1048576), (98, 2097152), (99, -1048576), (100, 1048576),
  (101, -1048576), (103, 1048576), (104, -2097152), (105, 1048576), (106, 1048576),
  (108, 1048576), (109, -1048576), (111, -1048576), (112, -1048576), (113, -1048576),
  (114, -1048576), (117, 1048576), (118, 1048576), (119, -1048576), (121, -1048576),
  (123, 1048576), (125, -1048576), (126, 1048576), (128, -1048576), (129, -1048576),
  (130, -1048576), (131, -1048576), (134, -1048576), (135, -1048576), (136, 1048576),
  (138, 1048576), (141, -1048576), (142, -1048576), (144, -1048576), (145, 1048576),
  (146, 3145728), (147, -1048576), (149, -2097152), (150, 1048576), (151, -1048576),
  (152, 1048576), (154, -1048576), (155, 2097152), (158, -1048576), (163, -1048576),
  (164, -1048576), (168, -1048576), (170, -1048576), (171, 1048576), (173, -1048576),
  (174, -1048576), (175, -1048576), (176, 1048576), (179, -1048576), (180, 1048576),
  (181, 1048576), (183, -1048576), (186, 1048576), (187, -1048576), (188, -1048576),
  (189, -1048576), (192, 1048576), (193, -1048576), (194, -1048576), (196, 1048576),
  (202, 1048576), (203, 1048576), (207, 1048576), (209, 1048576), (210, 1048576), (211, 1048576),
  (212, 1048576), (215, 1048576), (216, 1048576), (217, -1048576), (219, -1048576),
  (221, 3145728), (222, 1048576), (224, -2097152), (225, -1048576), (226, 1048576),
  (227, -1048576), (229, 1048576), (230, 2097152), (231, 1048576), (233, -2097152),
  (234, 1048576), (235, -1048576), (236, 1048576), (238, -1048576), (239, 2097152),
  (242, -1048576), (243, -1048576), (244, 1048576), (246, 1048576), (248, 1048576),
  (252, 1048576), (254, 1048576), (258, 1048576), (260, -3145728), (261, -1048576),
  (262, 1048576), (264, -1048576), (266, -1048576), (268, 1048576), (271, -1048576),
  (274, 1048576), (278, 3145728), (279, 1048576), (280, 1048576), (281, -1048576),
  (282, 1048576), (284, -1048576), (285, -1048576), (287, -1048576), (288, 1048576),
  (289, 1048576), (290, 1048576), (293, 1048576), (294, -1048576), (295, -1048576),
  (297, 1048576), (299, 1048576), (305, -1048576), (308, 1048576), (313, 1048576),
  (314, 1048576), (318, 1048576), (320, 1048576), (326, 1048576), (329, -1048576),
  (334, -1048576), (335, -1048576), (339, -1048576), (341, -1048576), (342, 1048576),
  (343, -1048576), (344, 1048576), (345, 1048576), (347, -1048576), (348, -1048576),
  (350, 1048576), (351, 1048576), (352, 1048576), (353, -1048576), (356, -1048576),
  (357, 1048576), (358, 1048576), (360, -1048576), (362, -1048576), (363, -1048576),
  (364, -3145728), (366, 1048576), (367, 1048576), (369, 1048576), (370, -3145728),
  (371, -1048576), (372, 1048576), (374, 2097152), (375, 1048576), (376, -1048576),
  (377, 1048576), (379, -1048576), (380, -2097152), (381, 3145728), (382, -1048576),
  (384, -1048576), (385, 1048576), (387, 1048576), (388, 1048576), (389, 1048576),
  (390, 1048576), (393, -1048576), (394, -1048576), (395, 1048576), (397, 1048576),
  (399, -1048576), (401, 1048576), (402, -1048576), (404, 1048576), (405, 1048576),
  (406, 1048576), (407, 1048576), (410, 1048576), (411, 1048576), (412, -1048576),
  (414, -1048576), (417, 1048576), (418, 1048576), (420, 1048576), (421, 3145728),
  (422, 1048576), (423, 1048576), (425, -2097152), (426, -1048576), (427, 1048576),
  (428, -1048576), (430, 1048576), (431, 2097152), (434, 1048576), (439, 1048576),
  (440, 1048576), (444, 1048576), (446, 1048576), (447, 3145728), (449, 1048576), (450, 1048576),
  (451, 1048576), (452, -1048576), (455, 1048576), (456, -1048576), (457, -1048576),
  (459, 1048576), (462, -1048576), (463, 1048576), (464, 1048576), (465, 1048576),
  (468, -1048576), (469, 1048576), (470, 1048576), (472, -1048576), (478, -1048576),
  (479, -1048576), (483, -1048576), (485, -1048576), (486, -1048576), (487, -1048576),
  (488, 3145728), (491, -1048576), (492, -1048576), (493, 1048576), (495, 1048576),
  (497, 1048576), (498, -1048576), (500, -2097152), (501, 1048576), (502, -1048576),
  (503, 1048576), (505, -1048576), (506, 2097152), (507, -1048576), (509, -2097152),
  (510, -1048576), (511, 1048576), (512, -1048576), (514, 1048576), (515, 2097152),
  (518, 1048576), (519, 1048576), (520, -1048576), (522, -1048576), (524, -1048576),
  (528, -1048576), (530, -1048576), (534, -1048576), (536, 3145728), (537, 1048576),
  (538, 3145728), (540, 1048576), (542, 1048576), (544, 3145728), (547, 1048576), (550, -1048576)]

/-- The octads of the incoming octad blocks, increasing. -/
def srcTenthOcts : List ℕ := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 55, 56, 57, 58, 59, 61, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 78,
  80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 98, 99, 100, 101, 102, 103,
  104, 105, 106, 107, 108, 109, 110, 111, 114, 115, 116, 117, 120, 121, 122, 123, 124, 125, 126,
  127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 141, 142, 143, 144, 145, 146,
  147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 165, 166, 167,
  168, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188,
  189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 204, 205, 206, 207, 209, 210,
  211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 227, 228, 230, 231,
  232, 233, 234, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 252, 253,
  254, 255, 256, 257, 259, 260, 262, 264, 265, 266, 269, 270, 271, 272, 273, 274, 275, 276, 277,
  278, 279, 280, 282, 283, 284, 287, 288, 289, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301,
  302, 303, 304, 305, 306, 307, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 321, 322, 323,
  324, 325, 327, 328, 329, 331, 333, 334, 335, 336, 338, 339, 340, 341, 342, 345, 346, 349, 350,
  351, 352, 354, 355, 356, 357, 358, 359, 362, 363, 364, 366, 367, 368, 369, 370, 371, 372, 373,
  374, 376, 377, 378, 379, 380, 381, 383, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395,
  397, 398, 399, 400, 401, 403, 404, 407, 408, 409, 411, 412, 413, 414, 415, 416, 417, 418, 419,
  420, 421, 422, 425, 426, 427, 428, 430, 431, 432, 433, 434, 435, 436, 437, 438, 440, 441, 442,
  443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461,
  462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480,
  481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 497, 498, 499, 500,
  501, 502, 503, 504, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520,
  522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540,
  542, 543, 544, 546, 547, 548, 549, 551, 552, 553, 554, 556, 557, 558, 559, 560, 561, 562, 563,
  564, 565, 566, 567, 568, 569, 570, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583,
  585, 586, 587, 588, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604,
  605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623,
  624, 625, 626, 627, 628, 629, 630, 631, 633, 634, 635, 636, 637, 638, 639, 641, 642, 643, 644,
  645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663,
  664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682,
  683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 698, 699, 700, 701, 702,
  703, 704, 705, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722,
  723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741,
  742, 743, 744, 746, 748, 749, 751, 752, 753, 754, 755, 756, 758]

/-- The denominator of the packed incoming tensor. -/
def srcTenthYDen : ℚ := (tensorWordDenAll srcTenthYWord : ℚ) * 1

/-- The Tenth axis as an identification vector. -/
def tenthSrcVec : IdentVec :=
  twTriVec 128 srcTenthYL srcTenthYX srcTenthYDen srcTenthMat
    srcTenthPairs srcTenthOcts 262144 2097152

/-- The packed tensor of the Tenth representation. -/
def tenthSrcX : List SVec := twTriTen 128 2097152 srcTenthYX srcTenthYL.sh.odd

/-- The incoming tensor denominator. -/
theorem srcTenthYDen_eq : srcTenthYDen = 16777216 := by
  unfold srcTenthYDen
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal matrix block agrees with the triality formula. -/
theorem tenthSrc_mat : twMatCheck srcTenthMat srcTenthYL = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels are below `552`. -/
theorem tenthSrc_pairRange : srcTenthPairs.all (fun q => decide (q.1 < 552)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `0` to `68`. -/
theorem tenthSrc_pairs00 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 0 0 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `69` to `137`. -/
theorem tenthSrc_pairs01 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 0 69 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `138` to `206`. -/
theorem tenthSrc_pairs02 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 0 138 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `207` to `275`. -/
theorem tenthSrc_pairs03 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 0 207 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `0` to `68`. -/
theorem tenthSrc_pairs10 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 1 0 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `69` to `137`. -/
theorem tenthSrc_pairs11 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 1 69 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `138` to `206`. -/
theorem tenthSrc_pairs12 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 1 138 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `207` to `275`. -/
theorem tenthSrc_pairs13 :
    srcPairChunk srcTenthPairs srcTenthYL 16777216 1 207 69 = true := by
  decide +kernel

/-- The literal pair terms agree with the triality formula. -/
theorem tenthSrc_pairs :
    twPairCheck srcTenthPairs srcTenthYL srcTenthYDen = true := by
  rw [srcTenthYDen_eq]
  apply srcTwPairCheck_of_chunks _ _ _ tenthSrc_pairRange
  intro s hs c hc
  interval_cases s <;> interval_cases c
  · exact tenthSrc_pairs00
  · exact tenthSrc_pairs01
  · exact tenthSrc_pairs02
  · exact tenthSrc_pairs03
  · exact tenthSrc_pairs10
  · exact tenthSrc_pairs11
  · exact tenthSrc_pairs12
  · exact tenthSrc_pairs13

set_option maxRecDepth 100000 in
/-- The octad list covers the incoming blocks. -/
theorem tenthSrc_octs : twOctCheck srcTenthOcts srcTenthYL = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem tenthSrc_oddBound :
    srcTenthYL.sh.odd.all
        (fun q => decide ((2097152 * q.2).natAbs ≤ 8388608)) = true ∧
      4 * (tensorWordGrowthAll srcTenthYWord * 64) +
        srcTenthYL.sh.odd.length * 8388608 < 2 ^ 128 := by
  decide +kernel

/-- The Tenth axis is represented exactly. -/
theorem tenthSrc_actual :
    griessConwayEncode generatedTenthAxis = tenthSrcVec.real := by
  rw [generatedTenthAxis_local_expression]
  apply twTriVec_actual 128 _ 8388608 srcTenthYL srcTenthYX srcTenthYDen srcTenthMat
    srcTenthPairs srcTenthOcts 262144 2097152 srcTenthYL_ok rfl
    (by rw [srcTenthYDen_eq]; norm_num)
    srcTenthYX_bnd tenthSrc_oddBound.1 tenthSrc_oddBound.2
  · change ((2097152 : ℤ) : ℚ) = 1 / 16 * (2 * srcTenthYDen)
    rw [srcTenthYDen_eq]
    norm_num
  · change ((262144 : ℤ) : ℚ) / (2 * srcTenthYDen) = 1 / 16 / 8
    rw [srcTenthYDen_eq]
    norm_num
  · exact tenthSrc_mat
  · exact tenthSrc_pairs
  · exact tenthSrc_octs
  · exact srcTenthYL_actual

/-- The representation of family representative `11`. -/
theorem tenthSrc_rep :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 11) =
      tenthSrcVec.real := tenthSrc_actual

/-- The short block of the Tenth representation satisfies the range conditions. -/
theorem tenthSrcVec_ok : tenthSrcVec.sh.ok = true :=
  twTriVec_ok _ _ _ _ _ _ _ _ _ tenthSrc_pairs tenthSrc_octs

/-- The tensor block of the Tenth representation. -/
theorem tenthSrcVec_ten :
    tenthSrcVec.ten = tensorRat 128 tenthSrcX (2 * srcTenthYDen) := rfl

/-- Bounds of the packed Tenth tensor. -/
theorem tenthSrcX_bnd :
    TBnd 128 (4 * (tensorWordGrowthAll srcTenthYWord * 64) +
      srcTenthYL.sh.odd.length * 8388608) tenthSrcX :=
  twTriTen_bnd 128 _ 8388608 2097152 srcTenthYX srcTenthYL.sh.odd srcTenthYX_bnd
    (fun q hq => by
      have h := tenthSrc_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    tenthSrc_oddBound.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
