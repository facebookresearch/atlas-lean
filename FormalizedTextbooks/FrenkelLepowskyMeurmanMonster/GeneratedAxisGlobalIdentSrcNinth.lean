/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcNinthL
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcChecks

/-! # The Ninth axis as an identification vector

`ninthSrcVec : IdentVec` represents the canonical Ninth axis `generatedNinthAxis` (family
representative `8`), the forward triality image of the incoming vector `srcNinthYL` (=
`srcNinthYVec`). It is the generic triality image `twTriVec` (worker gtwelfth) of the incoming
vector: odd short terms unpacked from the packed incoming tensor, octad blocks by the octad Fourier
transform, the packed tensor block by `trialityTensorT` plus the packed odd-short part; the matrix
block and the pair terms are literal data checked by the kernel against the triality formulas (the
pair check in eight blocks). `ninthSrc_rep` binds it to the genuine coordinates.
Density: 264 pair terms, 30472 octad terms in 729 octads, 30848 odd terms, 62968 tensor entries;
short scale `1 / 131072`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- The unit vector `e_i` or the sum `e_i + e_j`, materialized. -/
def srcNinthUnit (i j : ℕ) : List ℚ :=
  (List.range 24).map (fun t => if t = i ∨ t = j then 1 else 0)

/-- The literal matrix block of the Ninth axis: a multiple of the identity plus rank-one terms. -/
def srcNinthMat : MatRep :=
  ⟨(3 / 8 : ℚ), [
    ((1 / 16 : ℚ), srcNinthUnit 0 23), ((-1 / 16 : ℚ), srcNinthUnit 1 16),
    ((-1 / 16 : ℚ), srcNinthUnit 2 4), ((1 / 16 : ℚ), srcNinthUnit 6 17),
    ((-1 / 16 : ℚ), srcNinthUnit 7 22), ((1 / 16 : ℚ), srcNinthUnit 10 13),
    ((1 / 16 : ℚ), srcNinthUnit 14 15), ((-1 / 16 : ℚ), srcNinthUnit 19 21),
    ((-1 / 8 : ℚ), srcNinthUnit 0 0), ((-1 / 8 : ℚ), srcNinthUnit 6 6),
    ((-1 / 8 : ℚ), srcNinthUnit 10 10), ((-1 / 8 : ℚ), srcNinthUnit 13 13),
    ((-1 / 8 : ℚ), srcNinthUnit 14 14), ((-1 / 8 : ℚ), srcNinthUnit 15 15),
    ((-1 / 8 : ℚ), srcNinthUnit 17 17), ((-1 / 8 : ℚ), srcNinthUnit 23 23)]⟩

/-- The literal pair terms of the Ninth axis (short scale `1 / 131072`). -/
def srcNinthPairs : List (ℕ × ℤ) := [
  (2, 4096), (4, 4096), (7, 4096), (8, -4096), (10, -4096), (11, 4096), (17, 4096), (19, 4096),
  (24, 4096), (26, 4096), (29, -4096), (30, 4096), (32, -4096), (33, 4096), (37, -16384),
  (39, -4096), (41, -4096), (45, 4096), (46, -16384), (47, -4096), (50, -4096), (51, -4096),
  (53, 4096), (54, 4096), (60, 4096), (62, -4096), (66, -4096), (68, 4096), (69, 4096),
  (72, -4096), (75, -4096), (76, -4096), (77, -4096), (78, -4096), (79, 4096), (81, 4096),
  (83, -4096), (84, -4096), (85, 4096), (86, 4096), (89, 4096), (90, 4096), (92, -4096),
  (93, -4096), (99, -4096), (101, 4096), (105, 4096), (106, 4096), (109, 4096), (112, 4096),
  (113, 4096), (114, 4096), (115, -4096), (116, 4096), (118, -4096), (120, 4096), (121, -4096),
  (122, 4096), (124, -4096), (125, 4096), (127, 4096), (128, -4096), (134, 4096), (136, 4096),
  (140, 4096), (141, -4096), (143, 4096), (144, -4096), (150, -4096), (152, -4096),
  (154, -16384), (157, -4096), (160, -4096), (161, 4096), (162, 4096), (163, 4096), (164, -4096),
  (166, 4096), (168, -4096), (169, -4096), (170, 4096), (171, -4096), (174, -4096), (175, 4096),
  (176, 4096), (177, -4096), (178, 4096), (180, 4096), (182, -4096), (183, 4096), (184, -4096),
  (185, -4096), (186, -4096), (192, 4096), (194, -4096), (199, -4096), (200, 4096), (201, 4096),
  (202, 4096), (203, 4096), (205, -4096), (207, 4096), (208, -4096), (209, -4096), (210, -4096),
  (211, 4096), (212, 4096), (213, -4096), (214, -4096), (216, -4096), (218, 4096), (219, 4096),
  (220, 4096), (225, 4096), (227, -4096), (234, 4096), (236, -4096), (242, 4096), (244, -4096),
  (249, 4096), (251, 4096), (255, 4096), (257, 4096), (261, 4096), (263, -4096), (264, 4096),
  (265, 4096), (266, -4096), (267, -16384), (270, 4096), (271, 4096), (272, 4096), (278, -4096),
  (280, -4096), (283, -4096), (284, 4096), (286, 4096), (287, -4096), (293, -4096), (295, -4096),
  (298, -16384), (300, -4096), (302, -4096), (305, 4096), (306, -4096), (308, 4096),
  (309, -4096), (315, 4096), (317, 4096), (321, -4096), (323, 4096), (326, 4096), (327, 4096),
  (329, -4096), (330, -4096), (336, -4096), (338, 4096), (342, 4096), (344, -4096), (345, -4096),
  (348, 4096), (351, 4096), (352, 4096), (353, 4096), (354, 4096), (355, -4096), (357, -4096),
  (359, 4096), (360, 4096), (361, -4096), (362, -4096), (365, -4096), (366, -4096), (368, 4096),
  (369, 4096), (375, 4096), (377, -4096), (381, -4096), (382, -4096), (385, -4096), (388, -4096),
  (389, -4096), (390, -4096), (391, 4096), (392, -4096), (394, 4096), (396, -4096), (397, 4096),
  (398, -4096), (400, 4096), (401, -4096), (403, -4096), (404, 4096), (409, -16384),
  (410, -4096), (412, -4096), (416, -4096), (417, 4096), (419, -4096), (420, 4096), (426, 4096),
  (428, 4096), (433, 4096), (436, 4096), (437, -4096), (438, -4096), (439, -4096), (440, 4096),
  (442, -4096), (444, 4096), (445, 4096), (446, -4096), (447, 4096), (450, 4096), (451, -4096),
  (452, -4096), (453, 4096), (454, -4096), (456, -4096), (458, 4096), (459, -4096), (460, 4096),
  (461, 4096), (462, 4096), (463, -16384), (468, -4096), (470, 4096), (475, 4096), (476, -4096),
  (477, -4096), (478, -4096), (479, -4096), (481, 4096), (483, -4096), (484, 4096), (485, 4096),
  (486, 4096), (487, -4096), (488, -4096), (489, 4096), (490, 4096), (492, 4096), (494, -4096),
  (495, -4096), (496, -4096), (501, -4096), (503, 4096), (507, -16384), (510, -4096),
  (512, 4096), (518, -4096), (520, 4096), (525, -4096), (527, -4096), (531, -4096), (533, -4096),
  (537, -4096), (539, 4096), (540, -4096), (541, -4096), (542, 4096), (546, -4096), (547, -4096),
  (548, -4096)]

/-- The octads of the incoming octad blocks, increasing. -/
def srcNinthOcts : List ℕ := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74,
  75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98,
  99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
  119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137,
  138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156,
  157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
  176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194,
  195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 211, 212, 213, 214,
  215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 227, 228, 229, 230, 231, 232, 233, 234,
  235, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254,
  255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273,
  274, 275, 276, 277, 278, 279, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293,
  294, 295, 296, 297, 298, 299, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313,
  314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332,
  333, 334, 335, 336, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352,
  353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371,
  372, 373, 374, 375, 376, 377, 378, 379, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391,
  392, 393, 394, 395, 396, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411,
  412, 413, 414, 415, 416, 417, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431,
  432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450,
  451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469,
  470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488,
  489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507,
  508, 509, 510, 511, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527,
  528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 539, 540, 541, 542, 543, 544, 545, 547, 548,
  549, 550, 551, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 569,
  570, 571, 572, 573, 574, 575, 576, 577, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589,
  590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608,
  609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627,
  628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 644, 645, 646, 647,
  648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 665, 666, 667,
  668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686,
  687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 702, 703, 704, 705, 706,
  707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725,
  726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744,
  745, 746, 747, 748, 749, 750, 751, 752, 754, 755, 756, 758]

/-- The denominator of the packed incoming tensor. -/
def srcNinthYDen : ℚ := (tensorWordDenAll srcNinthYWord : ℚ) * 1

/-- The Ninth axis as an identification vector. -/
def ninthSrcVec : IdentVec :=
  twTriVec 128 srcNinthYL srcNinthYX srcNinthYDen srcNinthMat
    srcNinthPairs srcNinthOcts 1024 8192

/-- The packed tensor of the Ninth representation. -/
def ninthSrcX : List SVec := twTriTen 128 8192 srcNinthYX srcNinthYL.sh.odd

/-- The incoming tensor denominator. -/
theorem srcNinthYDen_eq : srcNinthYDen = 65536 := by
  unfold srcNinthYDen
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal matrix block agrees with the triality formula. -/
theorem ninthSrc_mat : twMatCheck srcNinthMat srcNinthYL = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels are below `552`. -/
theorem ninthSrc_pairRange : srcNinthPairs.all (fun q => decide (q.1 < 552)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `0` to `68`. -/
theorem ninthSrc_pairs00 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 0 0 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `69` to `137`. -/
theorem ninthSrc_pairs01 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 0 69 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `138` to `206`. -/
theorem ninthSrc_pairs02 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 0 138 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `0`, indices `207` to `275`. -/
theorem ninthSrc_pairs03 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 0 207 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `0` to `68`. -/
theorem ninthSrc_pairs10 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 1 0 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `69` to `137`. -/
theorem ninthSrc_pairs11 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 1 69 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `138` to `206`. -/
theorem ninthSrc_pairs12 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 1 138 69 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Pair check block: family `1`, indices `207` to `275`. -/
theorem ninthSrc_pairs13 :
    srcPairChunk srcNinthPairs srcNinthYL 65536 1 207 69 = true := by
  decide +kernel

/-- The literal pair terms agree with the triality formula. -/
theorem ninthSrc_pairs :
    twPairCheck srcNinthPairs srcNinthYL srcNinthYDen = true := by
  rw [srcNinthYDen_eq]
  apply srcTwPairCheck_of_chunks _ _ _ ninthSrc_pairRange
  intro s hs c hc
  interval_cases s <;> interval_cases c
  · exact ninthSrc_pairs00
  · exact ninthSrc_pairs01
  · exact ninthSrc_pairs02
  · exact ninthSrc_pairs03
  · exact ninthSrc_pairs10
  · exact ninthSrc_pairs11
  · exact ninthSrc_pairs12
  · exact ninthSrc_pairs13

set_option maxRecDepth 100000 in
/-- The octad list covers the incoming blocks. -/
theorem ninthSrc_octs : twOctCheck srcNinthOcts srcNinthYL = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem ninthSrc_oddBound :
    srcNinthYL.sh.odd.all
        (fun q => decide ((8192 * q.2).natAbs ≤ 32768)) = true ∧
      4 * (tensorWordGrowthAll srcNinthYWord * 64) +
        srcNinthYL.sh.odd.length * 32768 < 2 ^ 128 := by
  decide +kernel

/-- The Ninth axis is represented exactly. -/
theorem ninthSrc_actual :
    griessConwayEncode generatedNinthAxis = ninthSrcVec.real := by
  rw [generatedNinthAxis_local_expression]
  apply twTriVec_actual 128 _ 32768 srcNinthYL srcNinthYX srcNinthYDen srcNinthMat
    srcNinthPairs srcNinthOcts 1024 8192 srcNinthYL_ok rfl
    (by rw [srcNinthYDen_eq]; norm_num)
    srcNinthYX_bnd ninthSrc_oddBound.1 ninthSrc_oddBound.2
  · change ((8192 : ℤ) : ℚ) = 1 / 16 * (2 * srcNinthYDen)
    rw [srcNinthYDen_eq]
    norm_num
  · change ((1024 : ℤ) : ℚ) / (2 * srcNinthYDen) = 1 / 16 / 8
    rw [srcNinthYDen_eq]
    norm_num
  · exact ninthSrc_mat
  · exact ninthSrc_pairs
  · exact ninthSrc_octs
  · exact srcNinthYL_actual

/-- The representation of family representative `8`. -/
theorem ninthSrc_rep :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 8) =
      ninthSrcVec.real := ninthSrc_actual

/-- The short block of the Ninth representation satisfies the range conditions. -/
theorem ninthSrcVec_ok : ninthSrcVec.sh.ok = true :=
  twTriVec_ok _ _ _ _ _ _ _ _ _ ninthSrc_pairs ninthSrc_octs

/-- The tensor block of the Ninth representation. -/
theorem ninthSrcVec_ten :
    ninthSrcVec.ten = tensorRat 128 ninthSrcX (2 * srcNinthYDen) := rfl

/-- Bounds of the packed Ninth tensor. -/
theorem ninthSrcX_bnd :
    TBnd 128 (4 * (tensorWordGrowthAll srcNinthYWord * 64) +
      srcNinthYL.sh.odd.length * 32768) ninthSrcX :=
  twTriTen_bnd 128 _ 32768 8192 srcNinthYX srcNinthYL.sh.odd srcNinthYX_bnd
    (fun q hq => by
      have h := ninthSrc_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    ninthSrc_oddBound.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
