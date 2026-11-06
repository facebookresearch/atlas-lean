/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightL
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcChecks

/-! # The Root8 axis as an identification vector

`rootEightSrcVec : IdentVec` represents the canonical Root8 axis `generatedFifthRootEightAxis`
(family representative `9`), the forward triality image of the incoming vector `srcRootEightYL` (=
`srcRootEightYVec`). It is the generic triality image `twTriVec` (worker gtwelfth) of the incoming
vector: odd short terms unpacked from the packed incoming tensor, octad blocks by the octad Fourier
transform, the packed tensor block by `trialityTensorT` plus the packed odd-short part; the matrix
block and the pair terms are literal data checked by the kernel against the triality formulas (the
pair check in eight blocks). `rootEightSrc_rep` binds it to the genuine coordinates.
Density: 328 pair terms, 16864 octad terms in 407 octads, 16384 odd terms, 36624 tensor entries;
short scale `1 / 131072`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The unit vector `e_i` or the sum `e_i + e_j`, materialized. -/
def srcRootEightUnit (i j : ℕ) : List ℚ :=
  (List.range 24).map (fun t => if t = i ∨ t = j then 1 else 0)

/-- The literal matrix block of the Root8 axis: a multiple of the identity plus rank-one terms. -/
def srcRootEightMat : MatRep :=
  ⟨(5 / 16 : ℚ), [
    ((1 / 16 : ℚ), srcRootEightUnit 1 2), ((-1 / 16 : ℚ), srcRootEightUnit 1 8),
    ((1 / 16 : ℚ), srcRootEightUnit 1 11), ((-1 / 16 : ℚ), srcRootEightUnit 1 16),
    ((1 / 16 : ℚ), srcRootEightUnit 1 17), ((-1 / 16 : ℚ), srcRootEightUnit 1 18),
    ((-1 / 16 : ℚ), srcRootEightUnit 1 19), ((1 / 16 : ℚ), srcRootEightUnit 1 20),
    ((1 / 16 : ℚ), srcRootEightUnit 1 22), ((-1 / 16 : ℚ), srcRootEightUnit 2 8),
    ((1 / 16 : ℚ), srcRootEightUnit 2 11), ((-1 / 16 : ℚ), srcRootEightUnit 2 16),
    ((1 / 16 : ℚ), srcRootEightUnit 2 17), ((-1 / 16 : ℚ), srcRootEightUnit 2 18),
    ((-1 / 16 : ℚ), srcRootEightUnit 2 19), ((1 / 16 : ℚ), srcRootEightUnit 2 20),
    ((1 / 16 : ℚ), srcRootEightUnit 2 22), ((-1 / 16 : ℚ), srcRootEightUnit 8 11),
    ((1 / 16 : ℚ), srcRootEightUnit 8 16), ((-1 / 16 : ℚ), srcRootEightUnit 8 17),
    ((1 / 16 : ℚ), srcRootEightUnit 8 18), ((1 / 16 : ℚ), srcRootEightUnit 8 19),
    ((-1 / 16 : ℚ), srcRootEightUnit 8 20), ((-1 / 16 : ℚ), srcRootEightUnit 8 22),
    ((-1 / 16 : ℚ), srcRootEightUnit 11 16), ((1 / 16 : ℚ), srcRootEightUnit 11 17),
    ((-1 / 16 : ℚ), srcRootEightUnit 11 18), ((-1 / 16 : ℚ), srcRootEightUnit 11 19),
    ((1 / 16 : ℚ), srcRootEightUnit 11 20), ((1 / 16 : ℚ), srcRootEightUnit 11 22),
    ((-1 / 8 : ℚ), srcRootEightUnit 16 17), ((1 / 16 : ℚ), srcRootEightUnit 16 18),
    ((1 / 16 : ℚ), srcRootEightUnit 16 19), ((-1 / 16 : ℚ), srcRootEightUnit 16 20),
    ((-1 / 16 : ℚ), srcRootEightUnit 16 22), ((-1 / 16 : ℚ), srcRootEightUnit 17 18),
    ((-1 / 16 : ℚ), srcRootEightUnit 17 19), ((1 / 16 : ℚ), srcRootEightUnit 17 20),
    ((1 / 16 : ℚ), srcRootEightUnit 17 22), ((1 / 16 : ℚ), srcRootEightUnit 18 19),
    ((-1 / 16 : ℚ), srcRootEightUnit 18 20), ((-1 / 16 : ℚ), srcRootEightUnit 18 22),
    ((-1 / 16 : ℚ), srcRootEightUnit 19 20), ((-1 / 16 : ℚ), srcRootEightUnit 19 22),
    ((1 / 16 : ℚ), srcRootEightUnit 20 22), ((1 / 4 : ℚ), srcRootEightUnit 8 8),
    ((1 / 4 : ℚ), srcRootEightUnit 16 16), ((1 / 4 : ℚ), srcRootEightUnit 18 18),
    ((1 / 4 : ℚ), srcRootEightUnit 19 19)]⟩

/-- The literal pair terms of the Root8 axis (short scale `1 / 131072`). -/
def srcRootEightPairs : List (ℕ × ℤ) := [
  (0, 4096), (1, 4096), (2, 8192), (7, -4096), (10, 4096), (17, 4096), (18, -4096), (19, -4096),
  (21, -4096), (23, 8192), (24, 4096), (25, 4096), (26, 4096), (27, -4096), (28, -4096),
  (29, -8192), (30, 4096), (31, -4096), (32, -8192), (33, -4096), (34, -4096), (35, -4096),
  (36, -4096), (37, 12288), (38, 4096), (39, -8192), (40, 8192), (41, 8192), (42, -4096),
  (43, 8192), (44, -4096), (45, 4096), (46, -4096), (47, -4096), (48, 4096), (49, 4096),
  (50, -8192), (51, 4096), (52, -4096), (53, -8192), (54, 4096), (55, 4096), (56, 4096),
  (57, 4096), (58, 12288), (59, 4096), (60, -8192), (61, 8192), (62, 8192), (63, -4096),
  (64, 8192), (65, -4096), (70, -4096), (73, 4096), (80, 4096), (81, -4096), (82, -4096),
  (84, -4096), (89, 4096), (92, 4096), (94, -8192), (99, 4096), (100, 4096), (101, -4096),
  (103, 4096), (107, -4096), (110, -4096), (114, -8192), (117, -4096), (118, -4096),
  (119, -4096), (121, 4096), (124, 4096), (127, 4096), (128, 8192), (134, -4096), (135, -4096),
  (136, -4096), (138, 4096), (140, -4096), (143, -4096), (146, 8192), (150, 4096), (151, 4096),
  (152, -4096), (154, 4096), (156, -4096), (157, 4096), (158, 8192), (159, 4096), (160, -4096),
  (161, -4096), (162, 4096), (163, -4096), (164, -12288), (165, 8192), (166, -8192),
  (167, -8192), (168, -4096), (169, -8192), (170, -4096), (171, -8192), (172, 4096),
  (179, -4096), (180, 4096), (181, 4096), (183, 4096), (185, -4096), (192, 4096), (193, -4096),
  (194, -4096), (196, -4096), (198, 4096), (199, -4096), (200, -4096), (201, 4096),
  (202, -12288), (203, -4096), (204, 8192), (205, -8192), (206, -8192), (207, 4096),
  (208, -8192), (209, 4096), (215, -4096), (216, -4096), (217, -4096), (219, 4096), (225, -4096),
  (226, -4096), (227, 4096), (229, -4096), (234, 4096), (235, 4096), (236, -4096), (238, 4096),
  (242, 4096), (243, 4096), (244, 4096), (246, -4096), (248, 8192), (249, -4096), (250, 4096),
  (251, 12288), (253, 12288), (255, -12288), (256, 12288), (257, 4096), (259, 4096),
  (261, -8192), (262, -8192), (263, 4096), (264, -8192), (265, 4096), (266, 8192), (267, -4096),
  (268, 8192), (269, -4096), (270, 4096), (271, 8192), (272, 4096), (273, 4096), (274, 8192),
  (275, 4096), (276, -4096), (277, -4096), (278, -8192), (283, 4096), (286, -4096), (293, -4096),
  (294, 4096), (295, 4096), (297, 4096), (299, 8192), (300, -4096), (301, -4096), (302, -4096),
  (303, 4096), (304, 4096), (305, -8192), (306, -4096), (307, 4096), (308, -8192), (309, 4096),
  (310, 4096), (311, 4096), (312, 4096), (313, 4096), (314, 12288), (315, -8192), (316, 8192),
  (317, 8192), (318, 4096), (319, 8192), (320, 4096), (321, -4096), (322, 4096), (323, 4096),
  (324, -4096), (325, -4096), (326, -8192), (327, -4096), (328, 4096), (329, -8192),
  (330, -4096), (331, -4096), (332, -4096), (333, -4096), (334, 4096), (335, 12288),
  (336, -8192), (337, 8192), (338, 8192), (339, 4096), (340, 8192), (341, 4096), (346, 4096),
  (349, -4096), (356, -4096), (357, 4096), (358, 4096), (360, 4096), (365, -4096), (368, -4096),
  (370, 8192), (375, -4096), (376, -4096), (377, 4096), (379, -4096), (383, 4096), (386, 4096),
  (390, 8192), (393, 4096), (394, 4096), (395, 4096), (397, -4096), (400, -4096), (403, -4096),
  (404, -8192), (410, 4096), (411, 4096), (412, 4096), (414, -4096), (416, 4096), (419, 4096),
  (422, -8192), (426, -4096), (427, -4096), (428, 4096), (430, -4096), (432, 4096), (433, -4096),
  (434, 8192), (435, -4096), (436, 4096), (437, 4096), (438, -4096), (439, -12288), (440, -4096),
  (441, 8192), (442, -8192), (443, -8192), (444, 4096), (445, -8192), (446, 4096), (447, 8192),
  (448, -4096), (455, 4096), (456, -4096), (457, -4096), (459, -4096), (461, 4096), (468, -4096),
  (469, 4096), (470, 4096), (472, 4096), (474, -4096), (475, 4096), (476, 4096), (477, -4096),
  (478, -4096), (479, -12288), (480, 8192), (481, -8192), (482, -8192), (483, -4096),
  (484, -8192), (485, -4096), (491, 4096), (492, 4096), (493, 4096), (495, -4096), (501, 4096),
  (502, 4096), (503, -4096), (505, 4096), (510, -4096), (511, -4096), (512, 4096), (514, -4096),
  (518, -4096), (519, -4096), (520, -4096), (522, 4096), (524, 24576), (525, -12288),
  (526, 12288), (527, 4096), (529, 4096), (531, -4096), (532, 4096), (533, 12288), (535, 12288),
  (537, -8192), (538, -8192), (539, -4096), (540, -8192), (541, -4096), (542, 8192), (543, 4096),
  (544, 8192), (545, 4096), (546, -4096), (547, 8192), (548, -4096), (549, -4096), (550, -8192),
  (551, -4096)]

/-- The octads of the incoming octad blocks, increasing. -/
def srcRootEightOcts : List ℕ := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 50, 51, 52, 53, 54, 55, 56, 57,
  58, 59, 60, 61, 62, 63, 64, 65, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 138, 139, 140,
  141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 166, 167,
  168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 190, 191, 192, 193, 198, 199, 200, 201, 202,
  203, 204, 205, 206, 207, 208, 209, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
  234, 235, 236, 237, 238, 239, 240, 241, 246, 247, 248, 249, 252, 253, 254, 255, 258, 259, 264,
  265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 296, 297, 298, 299, 300, 301, 302, 303,
  304, 305, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332,
  333, 334, 335, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371,
  372, 373, 374, 375, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 416, 417, 418, 419, 420,
  421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 456, 457, 458, 459,
  460, 461, 462, 463, 464, 465, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488,
  489, 490, 491, 492, 493, 494, 495, 506, 507, 508, 509, 510, 519, 520, 521, 522, 523, 524, 525,
  526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 547, 548, 549, 550, 551, 552,
  553, 554, 555, 556, 557, 558, 571, 572, 573, 574, 579, 580, 581, 582, 583, 584, 585, 586, 587,
  588, 589, 590, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 615, 616, 617, 618,
  619, 620, 621, 622, 627, 628, 629, 630, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651,
  652, 653, 654, 655, 656, 657, 658, 659, 660, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680,
  701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 717, 718, 721, 722, 723, 724, 729,
  730, 731, 732, 735, 736, 741, 742, 743, 744, 749, 750, 753, 754, 755, 756]

/-- The denominator of the packed incoming tensor. -/
def srcRootEightYDen : ℚ := (tensorWordDenAll srcRootEightYWord : ℚ) * 1

/-- The Root8 axis as an identification vector. -/
def rootEightSrcVec : IdentVec :=
  twTriVec 128 srcRootEightYL srcRootEightYX srcRootEightYDen srcRootEightMat
    srcRootEightPairs srcRootEightOcts 1024 8192

/-- The packed tensor of the Root8 representation. -/
def rootEightSrcX : List SVec := twTriTen 128 8192 srcRootEightYX srcRootEightYL.sh.odd

/-- The incoming tensor denominator. -/
theorem srcRootEightYDen_eq : srcRootEightYDen = 65536 := by
  unfold srcRootEightYDen
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal matrix block agrees with the triality formula. -/
theorem rootEightSrc_mat : twMatCheck srcRootEightMat srcRootEightYL = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels are below `552`. -/
theorem rootEightSrc_pairRange : srcRootEightPairs.all (fun q => decide (q.1 < 552)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `0` to `68`. -/
theorem rootEightSrc_pairs00 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 0 0 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `69` to `137`. -/
theorem rootEightSrc_pairs01 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 0 69 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `138` to `206`. -/
theorem rootEightSrc_pairs02 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 0 138 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `207` to `275`. -/
theorem rootEightSrc_pairs03 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 0 207 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `0` to `68`. -/
theorem rootEightSrc_pairs10 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 1 0 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `69` to `137`. -/
theorem rootEightSrc_pairs11 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 1 69 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `138` to `206`. -/
theorem rootEightSrc_pairs12 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 1 138 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `207` to `275`. -/
theorem rootEightSrc_pairs13 :
    srcPairChunk srcRootEightPairs srcRootEightYL 65536 1 207 69 = true := by
  decide +kernel

/-- The literal pair terms agree with the triality formula. -/
theorem rootEightSrc_pairs :
    twPairCheck srcRootEightPairs srcRootEightYL srcRootEightYDen = true := by
  rw [srcRootEightYDen_eq]
  apply srcTwPairCheck_of_chunks _ _ _ rootEightSrc_pairRange
  intro s hs c hc
  interval_cases s <;> interval_cases c
  · exact rootEightSrc_pairs00
  · exact rootEightSrc_pairs01
  · exact rootEightSrc_pairs02
  · exact rootEightSrc_pairs03
  · exact rootEightSrc_pairs10
  · exact rootEightSrc_pairs11
  · exact rootEightSrc_pairs12
  · exact rootEightSrc_pairs13

set_option maxRecDepth 100000 in
/-- The octad list covers the incoming blocks. -/
theorem rootEightSrc_octs : twOctCheck srcRootEightOcts srcRootEightYL = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem rootEightSrc_oddBound :
    srcRootEightYL.sh.odd.all
        (fun q => decide ((8192 * q.2).natAbs ≤ 32768)) = true ∧
      4 * (tensorWordGrowthAll srcRootEightYWord * 64) +
        srcRootEightYL.sh.odd.length * 32768 < 2 ^ 128 := by
  decide +kernel

/-- The Root8 axis is represented exactly. -/
theorem rootEightSrc_actual :
    griessConwayEncode generatedFifthRootEightAxis = rootEightSrcVec.real := by
  rw [generatedFifthRootEightAxis_local_expression]
  apply twTriVec_actual 128 _ 32768 srcRootEightYL srcRootEightYX srcRootEightYDen srcRootEightMat
    srcRootEightPairs srcRootEightOcts 1024 8192 srcRootEightYL_ok rfl
    (by rw [srcRootEightYDen_eq]; norm_num)
    srcRootEightYX_bnd rootEightSrc_oddBound.1 rootEightSrc_oddBound.2
  · change ((8192 : ℤ) : ℚ) = 1 / 16 * (2 * srcRootEightYDen)
    rw [srcRootEightYDen_eq]
    norm_num
  · change ((1024 : ℤ) : ℚ) / (2 * srcRootEightYDen) = 1 / 16 / 8
    rw [srcRootEightYDen_eq]
    norm_num
  · exact rootEightSrc_mat
  · exact rootEightSrc_pairs
  · exact rootEightSrc_octs
  · exact srcRootEightYL_actual

/-- The representation of family representative `9`. -/
theorem rootEightSrc_rep :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 9) =
      rootEightSrcVec.real := rootEightSrc_actual

/-- The short block of the Root8 representation satisfies the range conditions. -/
theorem rootEightSrcVec_ok : rootEightSrcVec.sh.ok = true :=
  twTriVec_ok _ _ _ _ _ _ _ _ _ rootEightSrc_pairs rootEightSrc_octs

/-- The tensor block of the Root8 representation. -/
theorem rootEightSrcVec_ten :
    rootEightSrcVec.ten = tensorRat 128 rootEightSrcX (2 * srcRootEightYDen) := rfl

/-- Bounds of the packed Root8 tensor. -/
theorem rootEightSrcX_bnd :
    TBnd 128 (4 * (tensorWordGrowthAll srcRootEightYWord * 64) +
      srcRootEightYL.sh.odd.length * 32768) rootEightSrcX :=
  twTriTen_bnd 128 _ 32768 8192 srcRootEightYX srcRootEightYL.sh.odd srcRootEightYX_bnd
    (fun q hq => by
      have h := rootEightSrc_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    rootEightSrc_oddBound.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
