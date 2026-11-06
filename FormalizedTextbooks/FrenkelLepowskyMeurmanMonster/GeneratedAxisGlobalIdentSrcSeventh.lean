/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentTri

/-! # The Seventh axis as an identification vector

`seventhSrcVecW w : IdentVec` represents the Seventh representative (family representative `6`),
the forward triality image `sExtra (L · v_Odd)` of the original local word image: it is the
generic triality image `twTriVec` (worker `gtwelfth`) of `srcSeventhY w`, with the literal image
matrix block and image pair terms checked entrywise in the kernel against the triality formulas,
and the octad label list of the source blocks. `seventhSrcW_rep` binds it to the genuine
coordinates. Densities: 552 nonzero pair terms, 231 octad blocks of `64`
(Fourier images), odd terms read off the packed tensor; dense tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The indicator vector of two coordinates, materialized. -/
def srcPairVec (a b : ℕ) : List ℚ :=
  (List.range 24).map (fun j => if j = a ∨ j = b then 1 else 0)

/-- Decode packed pair terms: labels in 10-bit fields, numerators in 16-bit fields with offset
`32768`. -/
def srcDecodePairs (labs nums : ℕ) : ℕ → List (ℕ × ℤ)
  | 0 => []
  | n + 1 => ((labs &&& 1023 : ℕ), ((nums &&& 65535 : ℕ) : ℤ) - 32768) ::
      srcDecodePairs (labs >>> 10) (nums >>> 16) n

/-- Decode packed octad labels in 10-bit fields. -/
def srcDecodeOcts (v : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (v &&& 1023) :: srcDecodeOcts (v >>> 10) n

/-- The matrix check only depends on the matrix block, the short block and the short scale. -/
theorem srcTwMatCheck_congr (M' : MatRep) (L L' : IdentVec) (hm : L.mat = L'.mat)
    (hs : L.sh = L'.sh) (hd : L.sden = L'.sden) : twMatCheck M' L = twMatCheck M' L' := by
  unfold twMatCheck twTriMatEntry
  rw [hm, hs, hd]

/-- The pair check only depends on the matrix block, the short block and the short scale. -/
theorem srcTwPairCheck_congr (P' : List (ℕ × ℤ)) (L L' : IdentVec) (D : ℚ)
    (hm : L.mat = L'.mat) (hs : L.sh = L'.sh) (hd : L.sden = L'.sden) :
    twPairCheck P' L D = twPairCheck P' L' D := by
  unfold twPairCheck twTriPairEntry
  rw [hm, hs, hd]

/-- The octad check only depends on the short block. -/
theorem srcTwOctCheck_congr (os : List ℕ) (L L' : IdentVec) (hs : L.sh = L'.sh) :
    twOctCheck os L = twOctCheck os L' := by
  unfold twOctCheck
  rw [hs]

/-- The image matrix block of the Seventh axis. -/
def srcSeventhMat : MatRep := ⟨0, [
    ((9 / 32 : ℚ), unitList 0), ((9 / 32 : ℚ), unitList 1), ((9 / 32 : ℚ), unitList 2),
    ((9 / 32 : ℚ), unitList 3), ((9 / 32 : ℚ), unitList 4), ((9 / 32 : ℚ), unitList 5),
    ((9 / 32 : ℚ), unitList 6), ((9 / 32 : ℚ), unitList 7), ((9 / 32 : ℚ), unitList 8),
    ((9 / 32 : ℚ), unitList 9), ((9 / 32 : ℚ), unitList 10), ((9 / 32 : ℚ), unitList 11),
    ((17 / 32 : ℚ), unitList 12), ((17 / 32 : ℚ), unitList 13), ((17 / 32 : ℚ), unitList 14),
    ((17 / 32 : ℚ), unitList 15), ((1 / 32 : ℚ), unitList 16), ((1 / 32 : ℚ), unitList 17),
    ((17 / 32 : ℚ), unitList 18), ((1 / 32 : ℚ), unitList 19), ((9 / 32 : ℚ), unitList 20),
    ((9 / 32 : ℚ), unitList 21), ((9 / 32 : ℚ), unitList 22), ((9 / 32 : ℚ), unitList 23),
    ((1 / 8 : ℚ), srcPairVec 16 17), ((1 / 8 : ℚ), srcPairVec 16 19),
    ((1 / 8 : ℚ), srcPairVec 17 19)]⟩

/-- Packed octad labels (10-bit fields) of the Seventh source blocks. -/
@[irreducible] def srcSeventhOsPacked : ℕ :=
    0x6c1ac6a1846017c5e1745c16c5a0e4380dc360d4340cc320240801c060140400c0200400 |||
    (0x04c02fcbe2c4b02bcae2a4a829ca62749c26c9a2649825c962449023c8e1c4701bc6e1b4 <<< 288) |||
    (0xf425033f8fc3e4f83dcf63c4f03bcee394e438ce2374dc36cda334cc32cca324c831cc63 <<< 576) |||
    (0xd765d5745cd6d5b16b5a9695294952147519404fd3e4f53c4c5304bd2e4b513449114410 <<< 864) |||
    (0x7b5ec7ade5791e3789e1731cb729c9721ae6b5ac6adaa691a3689a1681866158460d825d <<< 1152) |||
    (0x3c8ee2e8b62c8ae268962488e1a8661885e168561484e0e8360c82dfe7f5fc7edfa7bdee <<< 1440) |||
    (0x0e82a06769d6749ce6e9b66c9ae629866097e5a9665895e4a9264891e469164490e3e8f6 <<< 1728) |||
    (0x4bcaedb9ee5b7edcb6ad3b46ceb22c6b16c4b0ec2aa2a7a9aa5a928fa3a8da328ba1684a <<< 2016) |||
    (0x2f <<< 2304)

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 0. -/
def srcSeventhP0 : List (ℕ × ℤ) := [
    (0, -256), (1, -256), (2, 256), (3, -256), (4, 256), (5, 256), (6, -256), (7, -256),
    (8, 256), (9, 256), (10, -256), (11, -768), (12, 768), (13, 768), (14, -768), (15, -256),
    (16, -256), (17, 768), (18, -256), (19, -256), (20, -256), (21, -256), (22, -256),
    (23, 256), (24, -256), (25, 256), (26, -256), (27, -256), (28, 256), (29, 256), (30, -256),
    (31, -256), (32, 256), (33, 768), (34, -768), (35, -768), (36, 768), (37, 256), (38, 256),
    (39, -768), (40, 256), (41, 256), (42, 256), (43, 256), (44, 256), (45, -256), (46, 256),
    (47, -256), (48, -256), (49, 256), (50, 256), (51, -256), (52, -256), (53, 256), (54, 768),
    (55, -768), (56, -768), (57, 768), (58, 256), (59, 256), (60, -768), (61, 256), (62, 256),
    (63, 256), (64, 256), (65, 256), (66, -256), (67, 256), (68, 256), (69, -256), (70, -256),
    (71, 256), (72, 256), (73, -256), (74, -768), (75, 768), (76, 768), (77, -768), (78, -256),
    (79, -256), (80, 768), (81, -256), (82, -256), (83, -256), (84, -256), (85, -256),
    (86, -256), (87, -256), (88, 256), (89, 256), (90, -256), (91, -256)]

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 1. -/
def srcSeventhP1 : List (ℕ × ℤ) := [
    (92, 256), (93, 768), (94, -768), (95, -768), (96, 768), (97, 256), (98, 256), (99, -768),
    (100, 256), (101, 256), (102, 256), (103, 256), (104, 256), (105, 256), (106, -256),
    (107, -256), (108, 256), (109, 256), (110, -256), (111, -768), (112, 768), (113, 768),
    (114, -768), (115, -256), (116, -256), (117, 768), (118, -256), (119, -256), (120, -256),
    (121, -256), (122, -256), (123, -256), (124, -256), (125, 256), (126, 256), (127, -256),
    (128, -768), (129, 768), (130, 768), (131, -768), (132, -256), (133, -256), (134, 768),
    (135, -256), (136, -256), (137, -256), (138, -256), (139, -256), (140, 256), (141, -256),
    (142, -256), (143, 256), (144, 768), (145, -768), (146, -768), (147, 768), (148, 256),
    (149, 256), (150, -768), (151, 256), (152, 256), (153, 256), (154, 256), (155, 256),
    (156, -256), (157, -256), (158, 256), (159, 768), (160, -768), (161, -768), (162, 768),
    (163, 256), (164, 256), (165, -768), (166, 256), (167, 256), (168, 256), (169, 256),
    (170, 256), (171, 256), (172, -256), (173, -768), (174, 768), (175, 768), (176, -768),
    (177, -256), (178, -256), (179, 768), (180, -256), (181, -256), (182, -256), (183, -256)]

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 2. -/
def srcSeventhP2 : List (ℕ × ℤ) := [
    (184, -256), (185, -256), (186, -768), (187, 768), (188, 768), (189, -768), (190, -256),
    (191, -256), (192, 768), (193, -256), (194, -256), (195, -256), (196, -256), (197, -256),
    (198, 768), (199, -768), (200, -768), (201, 768), (202, 256), (203, 256), (204, -768),
    (205, 256), (206, 256), (207, 256), (208, 256), (209, 256), (210, -2304), (211, -2304),
    (212, 2304), (213, 768), (214, 768), (215, -2304), (216, 768), (217, 768), (218, 768),
    (219, 768), (220, 768), (221, 2304), (222, -2304), (223, -768), (224, -768), (225, 2304),
    (226, -768), (227, -768), (228, -768), (229, -768), (230, -768), (231, -2304), (232, -768),
    (233, -768), (234, 2304), (235, -768), (236, -768), (237, -768), (238, -768), (239, -768),
    (240, 768), (241, 768), (242, -2304), (243, 768), (244, 768), (245, 768), (246, 768),
    (247, 768), (248, 1280), (249, -768), (250, 1280), (251, 256), (252, 256), (253, 256),
    (254, 256), (255, -768), (256, 1280), (257, 256), (258, 256), (259, 256), (260, 256),
    (261, -768), (262, -768), (263, -768), (264, -768), (265, -768), (266, 256), (267, 256),
    (268, 256), (269, 256), (270, 256), (271, 256), (272, 256), (273, 256), (274, 256),
    (275, 256)]

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 3. -/
def srcSeventhP3 : List (ℕ × ℤ) := [
    (276, 256), (277, 256), (278, -256), (279, 256), (280, -256), (281, -256), (282, 256),
    (283, 256), (284, -256), (285, -256), (286, 256), (287, 768), (288, -768), (289, -768),
    (290, 768), (291, 256), (292, 256), (293, -768), (294, 256), (295, 256), (296, 256),
    (297, 256), (298, 256), (299, -256), (300, 256), (301, -256), (302, 256), (303, 256),
    (304, -256), (305, -256), (306, 256), (307, 256), (308, -256), (309, -768), (310, 768),
    (311, 768), (312, -768), (313, -256), (314, -256), (315, 768), (316, -256), (317, -256),
    (318, -256), (319, -256), (320, -256), (321, 256), (322, -256), (323, 256), (324, 256),
    (325, -256), (326, -256), (327, 256), (328, 256), (329, -256), (330, -768), (331, 768),
    (332, 768), (333, -768), (334, -256), (335, -256), (336, 768), (337, -256), (338, -256),
    (339, -256), (340, -256), (341, -256), (342, 256), (343, -256), (344, -256), (345, 256),
    (346, 256), (347, -256), (348, -256), (349, 256), (350, 768), (351, -768), (352, -768),
    (353, 768), (354, 256), (355, 256), (356, -768), (357, 256), (358, 256), (359, 256),
    (360, 256), (361, 256), (362, 256), (363, 256), (364, -256), (365, -256), (366, 256),
    (367, 256)]

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 4. -/
def srcSeventhP4 : List (ℕ × ℤ) := [
    (368, -256), (369, -768), (370, 768), (371, 768), (372, -768), (373, -256), (374, -256),
    (375, 768), (376, -256), (377, -256), (378, -256), (379, -256), (380, -256), (381, -256),
    (382, 256), (383, 256), (384, -256), (385, -256), (386, 256), (387, 768), (388, -768),
    (389, -768), (390, 768), (391, 256), (392, 256), (393, -768), (394, 256), (395, 256),
    (396, 256), (397, 256), (398, 256), (399, 256), (400, 256), (401, -256), (402, -256),
    (403, 256), (404, 768), (405, -768), (406, -768), (407, 768), (408, 256), (409, 256),
    (410, -768), (411, 256), (412, 256), (413, 256), (414, 256), (415, 256), (416, -256),
    (417, 256), (418, 256), (419, -256), (420, -768), (421, 768), (422, 768), (423, -768),
    (424, -256), (425, -256), (426, 768), (427, -256), (428, -256), (429, -256), (430, -256),
    (431, -256), (432, 256), (433, 256), (434, -256), (435, -768), (436, 768), (437, 768),
    (438, -768), (439, -256), (440, -256), (441, 768), (442, -256), (443, -256), (444, -256),
    (445, -256), (446, -256), (447, -256), (448, 256), (449, 768), (450, -768), (451, -768),
    (452, 768), (453, 256), (454, 256), (455, -768), (456, 256), (457, 256), (458, 256),
    (459, 256)]

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 5. -/
def srcSeventhP5 : List (ℕ × ℤ) := [
    (460, 256), (461, 256), (462, 768), (463, -768), (464, -768), (465, 768), (466, 256),
    (467, 256), (468, -768), (469, 256), (470, 256), (471, 256), (472, 256), (473, 256),
    (474, -768), (475, 768), (476, 768), (477, -768), (478, -256), (479, -256), (480, 768),
    (481, -256), (482, -256), (483, -256), (484, -256), (485, -256), (486, 2304), (487, 2304),
    (488, -2304), (489, -768), (490, -768), (491, 2304), (492, -768), (493, -768), (494, -768),
    (495, -768), (496, -768), (497, -2304), (498, 2304), (499, 768), (500, 768), (501, -2304),
    (502, 768), (503, 768), (504, 768), (505, 768), (506, 768), (507, 2304), (508, 768),
    (509, 768), (510, -2304), (511, 768), (512, 768), (513, 768), (514, 768), (515, 768),
    (516, -768), (517, -768), (518, 2304), (519, -768), (520, -768), (521, -768), (522, -768),
    (523, -768), (524, 768), (525, 768), (526, 768), (527, -256), (528, -256), (529, -256),
    (530, -256), (531, 768), (532, 768), (533, -256), (534, -256), (535, -256), (536, -256),
    (537, 768), (538, 768), (539, 768), (540, 768), (541, 768), (542, -256), (543, -256),
    (544, -256), (545, -256), (546, -256), (547, -256), (548, -256), (549, -256), (550, -256),
    (551, -256)]

/-- The image pair terms of the Seventh axis (scale `1/8192`). -/
def srcSeventhP : List (ℕ × ℤ) := srcSeventhP0 ++
  srcSeventhP1 ++
  srcSeventhP2 ++
  srcSeventhP3 ++
  srcSeventhP4 ++
  srcSeventhP5

/-- The octad labels of the source blocks. -/
def srcSeventhOs : List ℕ := srcDecodeOcts srcSeventhOsPacked 231

/-- The spatial image `S e₀` of the first unit vector under the Seventh word. -/
def srcSeventhE0 : List ℚ := [
    (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ),
    (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ),
    (3 / 8 : ℚ), (-3 / 8 : ℚ), (-3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ),
    (-3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]

/-- The literal source matrix block `(1/4) I + 2 (S e₀)(S e₀)ᵀ` of `L · v_Odd`. -/
def srcSeventhYMat : MatRep := ⟨1 / 4, [(2, srcSeventhE0)]⟩

set_option maxRecDepth 100000 in
/-- The spatial image of `e₀` under the Seventh word. -/
theorem srcSeventh_spatial_e0 :
    spWordVec identSpatialAlphabet srcSeventhH (unitList 0) = srcSeventhE0 := by
  decide +kernel

/-- The source matrix block is the literal one. -/
theorem srcSeventhYMat_eq : oddSrcMat.act identSpatialAlphabet srcSeventhH = srcSeventhYMat := by
  change (⟨1 / 4, [(2, spWordVec identSpatialAlphabet srcSeventhH (unitList 0))]⟩ : MatRep) = _
  rw [srcSeventh_spatial_e0]
  rfl

/-- The pair terms of `L · v_Odd`, materialized. -/
def srcSeventhYPairs : List (ℕ × ℤ) := [(248, 1), (250, 1), (256, 1)]

set_option maxRecDepth 100000 in
/-- The materialized pair terms are those of the transported list. -/
theorem srcSeventhYPairs_eq : (ShortData.ofList srcSeventhT).pairs = srcSeventhYPairs := by
  decide +kernel

/-- The short block of `L · v_Odd` with materialized pair terms. -/
def srcSeventhYSh : ShortData :=
  ⟨srcSeventhYPairs, (ShortData.ofList srcSeventhT).oct, (ShortData.ofList srcSeventhT).odd⟩

/-- The materialized short block is the transported one. -/
theorem srcSeventhYSh_eq : srcSeventhYSh = ShortData.ofList srcSeventhT := by
  rw [srcSeventhYSh, ← srcSeventhYPairs_eq]

/-- The identification vector of `L · v_Odd` with literal matrix block and pair terms. -/
def srcSeventhYL (w : ℕ) : IdentVec :=
  ⟨srcSeventhYMat, srcSeventhYSh, 1 / 4,
    tensorRat w (srcSeventhYX w) ((tensorWordDenAll srcSeventhH : ℚ) * 1)⟩

/-- The literal vector is the word image vector. -/
theorem srcSeventhYL_eq (w : ℕ) : srcSeventhYL w = srcSeventhY w := by
  unfold srcSeventhYL srcSeventhY
  rw [srcSeventhYMat_eq, srcSeventhYSh_eq]

/-- The Seventh axis as an identification vector with tensor columns of width `w`. -/
def seventhSrcVecW (w : ℕ) : IdentVec :=
  twTriVec w (srcSeventhYL w) (srcSeventhYX w) ((tensorWordDenAll srcSeventhH : ℚ) * 1)
    srcSeventhMat srcSeventhP srcSeventhOs 256 2048

set_option maxRecDepth 100000 in
/-- The image matrix block is the triality image of the source blocks (width `0` instance). -/
theorem srcSeventhMat_check0 : twMatCheck srcSeventhMat (srcSeventhYL 0) = true := by
  decide +kernel

/-- One entry of the image pair check. -/
def srcSeventhPE (s p : ℕ) : Bool :=
  decide (lookupQ srcSeventhP (276 * s + p) / (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1)) =
    twTriPairEntry (srcSeventhYL 0) s p)

set_option maxRecDepth 100000 in
/-- Image pair check entries `0`..`45` of sign `0`. -/
theorem srcSeventhPE_0_0 : (List.range' 0 46).all (srcSeventhPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `46`..`91` of sign `0`. -/
theorem srcSeventhPE_0_46 : (List.range' 46 46).all (srcSeventhPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `92`..`137` of sign `0`. -/
theorem srcSeventhPE_0_92 : (List.range' 92 46).all (srcSeventhPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `138`..`183` of sign `0`. -/
theorem srcSeventhPE_0_138 : (List.range' 138 46).all (srcSeventhPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `184`..`229` of sign `0`. -/
theorem srcSeventhPE_0_184 : (List.range' 184 46).all (srcSeventhPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `230`..`275` of sign `0`. -/
theorem srcSeventhPE_0_230 : (List.range' 230 46).all (srcSeventhPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `0`..`45` of sign `1`. -/
theorem srcSeventhPE_1_0 : (List.range' 0 46).all (srcSeventhPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `46`..`91` of sign `1`. -/
theorem srcSeventhPE_1_46 : (List.range' 46 46).all (srcSeventhPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `92`..`137` of sign `1`. -/
theorem srcSeventhPE_1_92 : (List.range' 92 46).all (srcSeventhPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `138`..`183` of sign `1`. -/
theorem srcSeventhPE_1_138 : (List.range' 138 46).all (srcSeventhPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `184`..`229` of sign `1`. -/
theorem srcSeventhPE_1_184 : (List.range' 184 46).all (srcSeventhPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `230`..`275` of sign `1`. -/
theorem srcSeventhPE_1_230 : (List.range' 230 46).all (srcSeventhPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The image pair labels are pair labels. -/
theorem srcSeventhP_labels : srcSeventhP.all (fun q => decide (q.1 < 552)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- All entries of the image pair check, for one sign. -/
theorem srcSeventhPE_all (s : ℕ) (hs : s < 2) : (List.range 276).all (srcSeventhPE s) = true := by
  have h : List.range 276 = List.range' 0 46 ++ List.range' 46 46 ++ List.range' 92 46 ++
      List.range' 138 46 ++ List.range' 184 46 ++ List.range' 230 46 := by decide
  rw [h]
  simp only [List.all_append, Bool.and_eq_true]
  interval_cases s
  · exact ⟨⟨⟨⟨⟨srcSeventhPE_0_0, srcSeventhPE_0_46⟩, srcSeventhPE_0_92⟩, srcSeventhPE_0_138⟩,
      srcSeventhPE_0_184⟩, srcSeventhPE_0_230⟩
  · exact ⟨⟨⟨⟨⟨srcSeventhPE_1_0, srcSeventhPE_1_46⟩, srcSeventhPE_1_92⟩, srcSeventhPE_1_138⟩,
      srcSeventhPE_1_184⟩, srcSeventhPE_1_230⟩

/-- The image pair terms are the triality image of the source blocks (width `0` instance). -/
theorem srcSeventhP_check0 :
    twPairCheck srcSeventhP (srcSeventhYL 0) ((tensorWordDenAll srcSeventhH : ℚ) * 1) = true := by
  unfold twPairCheck
  rw [srcSeventhP_labels, Bool.true_and, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro p _
  have h := srcSeventhPE_all s.val s.isLt
  rw [List.all_eq_true] at h
  exact h p.val (List.mem_range.mpr p.isLt)

set_option maxRecDepth 100000 in
/-- The octad label list covers the source blocks (width `0` instance). -/
theorem srcSeventhOs_check0 : twOctCheck srcSeventhOs (srcSeventhYL 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd source terms scaled by `2048` are at most `6144` (width `0` instance). -/
theorem srcSeventh_odd_bound0 : (srcSeventhYL 0).sh.odd.all
    (fun q => decide (((2048 : ℤ) * q.2).natAbs ≤ 6144)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The source has `276` odd terms (width `0` instance). -/
theorem srcSeventh_odd_length0 : (srcSeventhYL 0).sh.odd.length = 276 := by
  decide +kernel

/-- The short block of the source does not depend on the width. -/
theorem srcSeventhYL_sh (w : ℕ) : (srcSeventhYL w).sh = (srcSeventhYL 0).sh := rfl

/-- The image matrix block is the triality image of the source blocks. -/
theorem srcSeventhMat_check (w : ℕ) : twMatCheck srcSeventhMat (srcSeventhYL w) = true := by
  rw [srcTwMatCheck_congr _ (srcSeventhYL w) (srcSeventhYL 0) rfl rfl rfl]
  exact srcSeventhMat_check0

/-- The image pair terms are the triality image of the source blocks. -/
theorem srcSeventhP_check (w : ℕ) :
    twPairCheck srcSeventhP (srcSeventhYL w) ((tensorWordDenAll srcSeventhH : ℚ) * 1) = true := by
  rw [srcTwPairCheck_congr _ (srcSeventhYL w) (srcSeventhYL 0) _ rfl rfl rfl]
  exact srcSeventhP_check0

/-- The octad label list covers the source blocks. -/
theorem srcSeventhOs_check (w : ℕ) : twOctCheck srcSeventhOs (srcSeventhYL w) = true := by
  rw [srcTwOctCheck_congr _ (srcSeventhYL w) (srcSeventhYL 0) rfl]
  exact srcSeventhOs_check0

/-- The odd source terms scaled by `2048` are at most `6144`. -/
theorem srcSeventh_odd_bound (w : ℕ) : (srcSeventhYL w).sh.odd.all
    (fun q => decide (((2048 : ℤ) * q.2).natAbs ≤ 6144)) = true := by
  rw [srcSeventhYL_sh]
  exact srcSeventh_odd_bound0

/-- The source has `276` odd terms. -/
theorem srcSeventh_odd_length (w : ℕ) : (srcSeventhYL w).sh.odd.length = 276 := by
  rw [srcSeventhYL_sh]
  exact srcSeventh_odd_length0

/-- The Seventh representative has the coordinates of `seventhSrcVecW w`. -/
theorem seventhSrcW_rep {w : ℕ} (hw : 31 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 6) = (seventhSrcVecW w).real := by
  rw [srcSeventh_rep_eq]
  apply twTriVec_actual w (16777216 * 8) 6144 (srcSeventhYL w) (srcSeventhYX w) _ srcSeventhMat
    srcSeventhP srcSeventhOs 256 2048 (by rw [srcSeventhYL_eq]; exact srcSeventhY_ok w) rfl
    (by rw [srcSeventhH_den]; norm_num) (srcSeventhYX_bnd (by omega)) (srcSeventh_odd_bound w)
  · rw [srcSeventh_odd_length]
    calc 4 * (16777216 * 8) + 276 * 6144 < 2 ^ 31 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  · change ((2048 : ℤ) : ℚ) = 1 / 4 * (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1))
    rw [srcSeventhH_den]
    norm_num
  · change ((256 : ℤ) : ℚ) / (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1)) = 1 / 4 / 8
    rw [srcSeventhH_den]
    norm_num
  · exact srcSeventhMat_check w
  · exact srcSeventhP_check w
  · exact srcSeventhOs_check w
  · rw [srcSeventhYL_eq]
    exact srcSeventhY_actual (by omega)

/-- The short block of the Seventh representation satisfies the range conditions. -/
theorem seventhSrcVecW_ok (w : ℕ) : (seventhSrcVecW w).sh.ok = true :=
  twTriVec_ok w _ _ _ _ _ _ _ _ (srcSeventhP_check w) (srcSeventhOs_check w)

/-- The tensor block of the Seventh representation. -/
theorem seventhSrcVecW_ten (w : ℕ) : (seventhSrcVecW w).ten =
    tensorRat w (twTriTen w 2048 (srcSeventhYX w) (srcSeventhYL w).sh.odd)
      (2 * ((tensorWordDenAll srcSeventhH : ℚ) * 1)) := rfl

/-- Bounds of the packed tensor block of the Seventh representation. -/
theorem seventhSrcVecW_bnd {w : ℕ} (hw : 31 ≤ w) :
    TBnd w (4 * (16777216 * 8) + 276 * 6144)
      (twTriTen w 2048 (srcSeventhYX w) (srcSeventhYL w).sh.odd) := by
  have h := twTriTen_bnd w (16777216 * 8) 6144 2048 (srcSeventhYX w) (srcSeventhYL w).sh.odd
    (srcSeventhYX_bnd (by omega)) (by simpa [List.all_eq_true] using srcSeventh_odd_bound w)
    (by rw [srcSeventh_odd_length]
        calc 4 * (16777216 * 8) + 276 * 6144 < 2 ^ 31 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw)
  rw [srcSeventh_odd_length] at h
  exact h

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
