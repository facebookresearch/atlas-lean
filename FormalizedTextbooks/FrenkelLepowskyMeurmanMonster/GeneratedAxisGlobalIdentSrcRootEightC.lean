/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCS

/-! # The Root8 axis as a cheap identification vector

`rootEightSrcVecC w : IdentVec` represents the Root8 axis (family representative `9`) with the
tensor block given by the widened compact literal `srcRootEightCXLit` (numerators over `32`, field
bound `15` at every width `w ≥ 4`) and short scale `1 / 128`. It is the triality image `twTriVec` of
the cheap incoming vector `srcRootEightYC`, whose tensor is the widened checkpoint
`srcRootEightCYLit` (`srcRootEightY_tensor_chain`); the literal matrix block, the octad labels and
the matrix check are those of `rootEightSrcVec`, the pair check is the rescaled one. The computed
tensor is replaced by the literal after one packed comparison (`rootEightX12_check`).
`rootEightSrcC_rep` binds it to the genuine coordinates (pattern of gtwelfth's `twelfthSrcVecC`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The cheap packed tensor of the incoming vector (numerators over `64`, width `24`). -/
def srcRootEightYXC : List SVec := twWidenT 4 24 srcRootEightCYLit

/-- Bounds of the cheap incoming tensor. -/
theorem srcRootEightYXC_bnd : TBnd 24 15 srcRootEightYXC := by
  have h := twWidenT_bnd 4 24 (by norm_num) srcRootEightCYLit
  norm_num at h
  exact h

/-- The parts of the source word carry the Fifth tensor to the cheap incoming tensor. -/
theorem srcRootEightY_tensor_chain :
    localTensorRepresentation (identWordFiber srcRootEightYWord)
        (generatedAxisGlobalRationalTensorReal (tensorRat 20 (fifthSrcXW 20) 1)) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 srcRootEightYXC 64) := by
  obtain ⟨d0, g0, d1, g1, d2, g2⟩ := srcRootEightC_dens
  rw [srcRootEightYWord_parts]
  simp only [identWordFiber_append, map_mul, LinearEquiv.mul_apply]
  have a0 := tensorWordAll_actual srcRootEightCW0
    (fifthSrcXW_bnd (w := 20) (by norm_num))
    (by rw [g0]; norm_num) 1
  rw [g0] at a0
  rw [a0.2, d0, twColCheck_rat 20 2 4 _ _ _ (by norm_num) a0.1 (by norm_num)
    srcRootEightC_check0 _ 8 (by norm_num) (by norm_num),
    ← twWidenT_rat 2 16 (by norm_num) srcRootEightCL0 8]
  have a1 := tensorWordAll_actual srcRootEightCW1
    (twWidenT_bnd 2 16 (by norm_num) srcRootEightCL0)
    (by rw [g1]; norm_num) 8
  rw [g1] at a1
  rw [a1.2, d1, twColCheck_rat 16 2 32 _ _ _ (by norm_num) a1.1 (by norm_num)
    srcRootEightC_check1 _ 8 (by norm_num) (by norm_num),
    ← twWidenT_rat 2 16 (by norm_num) srcRootEightCL1 8]
  have a2 := tensorWordAll_actual srcRootEightCW2
    (twWidenT_bnd 2 16 (by norm_num) srcRootEightCL1)
    (by rw [g2]; norm_num) 8
  rw [g2] at a2
  rw [a2.2, d2, twColCheck_rat 16 4 8 _ _ _ (by norm_num) a2.1 (by norm_num)
    srcRootEightC_check2 _ 64 (by norm_num) (by norm_num),
    ← twWidenT_rat 4 24 (by norm_num) srcRootEightCYLit 64]
  rfl

/-- The incoming Root8 vector with the literal matrix block and the cheap tensor. -/
def srcRootEightYC : IdentVec :=
  ⟨srcRootEightYMat, ShortData.ofList srcRootEightYT, 1 / 16, tensorRat 24 srcRootEightYXC 64⟩

/-- The cheap incoming representation is exact. -/
theorem srcRootEightYC_actual :
    griessConwayEncode (rhoLocal generatedFifthRootEightLocal generatedFifthAxis) =
        srcRootEightYC.real := by
  have hT' : localTensorRepresentation
      (identWordFiber ((srcWordData srcRootEightYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal (fifthSrcVecW 20).ten) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 srcRootEightYXC 64) := by
    rw [srcWordData_fst]
    exact srcRootEightY_tensor_chain
  have h := IdentVec.word_actual (fifthSrcVecW 20) (srcWordData srcRootEightYWord)
      srcRootEightY_letters
    srcRootEightYD srcRootEightY_composite.1 srcRootEightY_composite.2.1 srcRootEightY_composite.2.2
        srcRootEightYT
    srcRootEightY_short _ hT' _ (fifthSrcW_rep (by norm_num))
  rw [srcWordData_fst] at h
  rw [← srcRootEightYWord_local]
  change griessConwayEncode (rhoLocal (identWordLocal srcRootEightYWord)
    (generatedAxisGlobalTwelveRepresentative 4)) = _
  rw [h]
  unfold srcRootEightYC
  rw [← srcRootEightYMat_eq]
  rfl

/-- The short block of the cheap incoming representation satisfies the range conditions. -/
theorem srcRootEightYC_ok : srcRootEightYC.sh.ok = true := ofList_ok _ srcRootEightY_labels

/-- The short scale of the cheap incoming representation. -/
theorem srcRootEightYC_sden : srcRootEightYC.sden = 1 / 16 := rfl

set_option maxRecDepth 100000 in
/-- The pair terms at short scale `1 / 128`. -/
def srcRootEightCPairs : List (ℕ × ℤ) :=
  [(0, 4), (1, 4), (2, 8), (7, -4), (10, 4), (17, 4), (18, -4), (19, -4), (21, -4), (23, 8),
    (24, 4), (25, 4), (26, 4), (27, -4), (28, -4), (29, -8), (30, 4), (31, -4), (32, -8),
    (33, -4), (34, -4), (35, -4), (36, -4), (37, 12), (38, 4), (39, -8), (40, 8), (41, 8),
    (42, -4), (43, 8), (44, -4), (45, 4), (46, -4), (47, -4), (48, 4), (49, 4), (50, -8),
    (51, 4), (52, -4), (53, -8), (54, 4), (55, 4), (56, 4), (57, 4), (58, 12), (59, 4), (60, -8),
    (61, 8), (62, 8), (63, -4), (64, 8), (65, -4), (70, -4), (73, 4), (80, 4), (81, -4),
    (82, -4), (84, -4), (89, 4), (92, 4), (94, -8), (99, 4), (100, 4), (101, -4), (103, 4),
    (107, -4), (110, -4), (114, -8), (117, -4), (118, -4), (119, -4), (121, 4), (124, 4),
    (127, 4), (128, 8), (134, -4), (135, -4), (136, -4), (138, 4), (140, -4), (143, -4),
    (146, 8), (150, 4), (151, 4), (152, -4), (154, 4), (156, -4), (157, 4), (158, 8), (159, 4),
    (160, -4), (161, -4), (162, 4), (163, -4), (164, -12), (165, 8), (166, -8), (167, -8),
    (168, -4), (169, -8), (170, -4), (171, -8), (172, 4), (179, -4), (180, 4), (181, 4),
    (183, 4), (185, -4), (192, 4), (193, -4), (194, -4), (196, -4), (198, 4), (199, -4),
    (200, -4), (201, 4), (202, -12), (203, -4), (204, 8), (205, -8), (206, -8), (207, 4),
    (208, -8), (209, 4), (215, -4), (216, -4), (217, -4), (219, 4), (225, -4), (226, -4),
    (227, 4), (229, -4), (234, 4), (235, 4), (236, -4), (238, 4), (242, 4), (243, 4), (244, 4),
    (246, -4), (248, 8), (249, -4), (250, 4), (251, 12), (253, 12), (255, -12), (256, 12),
    (257, 4), (259, 4), (261, -8), (262, -8), (263, 4), (264, -8), (265, 4), (266, 8), (267, -4),
    (268, 8), (269, -4), (270, 4), (271, 8), (272, 4), (273, 4), (274, 8), (275, 4), (276, -4),
    (277, -4), (278, -8), (283, 4), (286, -4), (293, -4), (294, 4), (295, 4), (297, 4), (299, 8),
    (300, -4), (301, -4), (302, -4), (303, 4), (304, 4), (305, -8), (306, -4), (307, 4),
    (308, -8), (309, 4), (310, 4), (311, 4), (312, 4), (313, 4), (314, 12), (315, -8), (316, 8),
    (317, 8), (318, 4), (319, 8), (320, 4), (321, -4), (322, 4), (323, 4), (324, -4), (325, -4),
    (326, -8), (327, -4), (328, 4), (329, -8), (330, -4), (331, -4), (332, -4), (333, -4),
    (334, 4), (335, 12), (336, -8), (337, 8), (338, 8), (339, 4), (340, 8), (341, 4), (346, 4),
    (349, -4), (356, -4), (357, 4), (358, 4), (360, 4), (365, -4), (368, -4), (370, 8),
    (375, -4), (376, -4), (377, 4), (379, -4), (383, 4), (386, 4), (390, 8), (393, 4), (394, 4),
    (395, 4), (397, -4), (400, -4), (403, -4), (404, -8), (410, 4), (411, 4), (412, 4),
    (414, -4), (416, 4), (419, 4), (422, -8), (426, -4), (427, -4), (428, 4), (430, -4),
    (432, 4), (433, -4), (434, 8), (435, -4), (436, 4), (437, 4), (438, -4), (439, -12),
    (440, -4), (441, 8), (442, -8), (443, -8), (444, 4), (445, -8), (446, 4), (447, 8),
    (448, -4), (455, 4), (456, -4), (457, -4), (459, -4), (461, 4), (468, -4), (469, 4),
    (470, 4), (472, 4), (474, -4), (475, 4), (476, 4), (477, -4), (478, -4), (479, -12),
    (480, 8), (481, -8), (482, -8), (483, -4), (484, -8), (485, -4), (491, 4), (492, 4),
    (493, 4), (495, -4), (501, 4), (502, 4), (503, -4), (505, 4), (510, -4), (511, -4), (512, 4),
    (514, -4), (518, -4), (519, -4), (520, -4), (522, 4), (524, 24), (525, -12), (526, 12),
    (527, 4), (529, 4), (531, -4), (532, 4), (533, 12), (535, 12), (537, -8), (538, -8),
    (539, -4), (540, -8), (541, -4), (542, 8), (543, 4), (544, 8), (545, 4), (546, -4), (547, 8),
    (548, -4), (549, -4), (550, -8), (551, -4)]

set_option maxRecDepth 100000 in
/-- The literal pair terms of `rootEightSrcVec` are the pair terms at short scale `1 / 128`,
rescaled. -/
theorem srcRootEightCPairs_scale : srcRootEightPairs = srcRootEightCPairs.map (fun q => (q.1, 1024 *
    q.2)) := by
  decide +kernel

/-- The literal pair terms agree with the triality formula at short scale `1 / 128`. -/
theorem rootEightSrcC_pairs : twPairCheck srcRootEightCPairs srcRootEightYC 64 = true := by
  rw [srcTwPairCheck_congr _ srcRootEightYC srcRootEightYL 64 rfl rfl rfl,
    ← srcTwPairCheck_scale srcRootEightCPairs 1024 srcRootEightYL srcRootEightYDen 64 (by norm_num)
      (by rw [srcRootEightYDen_eq]; norm_num), ← srcRootEightCPairs_scale]
  exact rootEightSrc_pairs

/-- The literal matrix block agrees with the triality formula. -/
theorem rootEightSrcC_mat : twMatCheck srcRootEightMat srcRootEightYC = true := by
  rw [srcTwMatCheck_congr _ srcRootEightYC srcRootEightYL rfl rfl rfl]
  exact rootEightSrc_mat

/-- The octad list covers the incoming octad blocks. -/
theorem rootEightSrcC_octs : twOctCheck srcRootEightOcts srcRootEightYC = true := by
  rw [srcTwOctCheck_congr _ srcRootEightYC srcRootEightYL rfl]
  exact rootEightSrc_octs

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem rootEightSrcC_oddBound :
    srcRootEightYC.sh.odd.all (fun q => decide ((8 * q.2).natAbs ≤ 32)) = true ∧
      4 * 15 + srcRootEightYC.sh.odd.length * 32 + 60 < 2 ^ 24 := by
  decide +kernel

/-- The triality image of the cheap incoming vector (short scale `1 / 128`). -/
def rootEightSrcVecC0 : IdentVec :=
  twTriVec 24 srcRootEightYC srcRootEightYXC 64 srcRootEightMat srcRootEightCPairs srcRootEightOcts
      1 8

/-- The triality image of the cheap incoming vector represents the Root8 axis. -/
theorem rootEightSrcC0_actual : griessConwayEncode generatedFifthRootEightAxis =
    rootEightSrcVecC0.real := by
  rw [generatedFifthRootEightAxis_local_expression]
  exact twTriVec_actual 24 15 32 srcRootEightYC srcRootEightYXC 64 srcRootEightMat
      srcRootEightCPairs srcRootEightOcts 1 8
    srcRootEightYC_ok rfl (by norm_num) srcRootEightYXC_bnd rootEightSrcC_oddBound.1
    (by have := rootEightSrcC_oddBound.2; omega)
    (by rw [srcRootEightYC_sden]; norm_num) (by rw [srcRootEightYC_sden]; norm_num)
    rootEightSrcC_mat rootEightSrcC_pairs rootEightSrcC_octs _ srcRootEightYC_actual

/-- The computed packed tensor of the triality image (numerators over `128`). -/
def rootEightX12C : List SVec := twTriTen 24 8 srcRootEightYXC srcRootEightYC.sh.odd

/-- Bounds of the computed packed tensor. -/
theorem rootEightX12C_bnd : TBnd 24 (4 * 15 + srcRootEightYC.sh.odd.length * 32) rootEightX12C :=
  twTriTen_bnd 24 15 32 8 srcRootEightYXC srcRootEightYC.sh.odd srcRootEightYXC_bnd
    (fun q hq => by
      have h := rootEightSrcC_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    (by have := rootEightSrcC_oddBound.2; omega)

set_option maxRecDepth 100000 in
/-- The computed tensor is four times the compact literal. -/
theorem rootEightX12_check : twColCheck 24 4 4 rootEightX12C srcRootEightCXLit = true := by
  decide +kernel

/-- The Root8 axis with the compact literal tensor block. -/
def rootEightSrcVecC (w : ℕ) : IdentVec :=
  ⟨srcRootEightMat, rootEightSrcVecC0.sh, rootEightSrcVecC0.sden, tensorRat w (twWidenT 4 w
      srcRootEightCXLit) 32⟩

/-- The compact tensor block is the computed tensor block. -/
theorem rootEightSrcVecC_ten_eq (w : ℕ) (hw : 4 ≤ w) :
    (rootEightSrcVecC w).ten = rootEightSrcVecC0.ten := by
  change tensorRat w (twWidenT 4 w srcRootEightCXLit) 32 = tensorRat 24 rootEightX12C (2 * 64)
  rw [twWidenT_rat 4 w hw]
  exact (twColCheck_rat 24 4 4 _ rootEightX12C srcRootEightCXLit (by norm_num) rootEightX12C_bnd
    (by have := rootEightSrcC_oddBound.2; omega) rootEightX12_check (2 * 64) 32 (by norm_num)
    (by norm_num)).symm

/-- The compact representation has the coordinates of the computed one. -/
theorem rootEightSrcVecC_real (w : ℕ) (hw : 4 ≤ w) :
    (rootEightSrcVecC w).real = rootEightSrcVecC0.real := by
  have ht := rootEightSrcVecC_ten_eq w hw
  unfold IdentVec.real IdentVec.packet
  rw [ht]
  rfl

/-- The representation of family representative `9` with the compact tensor. -/
theorem rootEightSrcC_rep (w : ℕ) (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 9) =
      (rootEightSrcVecC w).real := by
  rw [rootEightSrcVecC_real w hw]
  exact rootEightSrcC0_actual

/-- The short block of the compact representation satisfies the range conditions. -/
theorem rootEightSrcVecC_ok (w : ℕ) : (rootEightSrcVecC w).sh.ok = true := by
  change rootEightSrcVecC0.sh.ok = true
  exact twTriVec_ok 24 srcRootEightYC srcRootEightYXC 64 srcRootEightMat srcRootEightCPairs
      srcRootEightOcts 1 8
    rootEightSrcC_pairs rootEightSrcC_octs

/-- The short scale of the compact representation. -/
theorem rootEightSrcVecC_sden (w : ℕ) : (rootEightSrcVecC w).sden = 1 / 128 := by
  change 1 / (2 * (64 : ℚ)) = 1 / 128
  norm_num

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
