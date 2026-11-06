/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCS

/-! # The Tenth axis as a cheap identification vector

`tenthSrcVecC w : IdentVec` represents the Tenth axis (family representative `11`) with the tensor
block given by the widened compact literal `srcTenthCXLit` (numerators over `32`, field bound `15`
at every width `w ≥ 4`) and short scale `1 / 128`. It is the triality image `twTriVec` of the cheap
incoming vector `srcTenthYC`, whose tensor is the widened checkpoint `srcTenthCYLit`
(`srcTenthY_tensor_chain`); the literal matrix block, the octad labels and the matrix check are
those of `tenthSrcVec`, the pair check is the rescaled one. The computed tensor is replaced by the
literal after one packed comparison (`tenthX12_check`). `tenthSrcC_rep` binds it to the genuine
coordinates (pattern of gtwelfth's `twelfthSrcVecC`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The cheap packed tensor of the incoming vector (numerators over `64`, width `24`). -/
def srcTenthYXC : List SVec := twWidenT 4 24 srcTenthCYLit

/-- Bounds of the cheap incoming tensor. -/
theorem srcTenthYXC_bnd : TBnd 24 15 srcTenthYXC := by
  have h := twWidenT_bnd 4 24 (by norm_num) srcTenthCYLit
  norm_num at h
  exact h

/-- The parts of the source word carry the Fifth tensor to the cheap incoming tensor. -/
theorem srcTenthY_tensor_chain :
    localTensorRepresentation (identWordFiber srcTenthYWord)
        (generatedAxisGlobalRationalTensorReal (tensorRat 24 (fifthSrcXW 24) 1)) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 srcTenthYXC 64) := by
  obtain ⟨d0, g0, d1, g1, d2, g2, d3, g3⟩ := srcTenthC_dens
  rw [srcTenthYWord_parts]
  simp only [identWordFiber_append, map_mul, LinearEquiv.mul_apply]
  have a0 := tensorWordAll_actual srcTenthCW0
    (fifthSrcXW_bnd (w := 24) (by norm_num))
    (by rw [g0]; norm_num) 1
  rw [g0] at a0
  rw [a0.2, d0, twColCheck_rat 24 2 32 _ _ _ (by norm_num) a0.1 (by norm_num)
    srcTenthC_check0 _ 8 (by norm_num) (by norm_num),
    ← twWidenT_rat 2 16 (by norm_num) srcTenthCL0 8]
  have a1 := tensorWordAll_actual srcTenthCW1
    (twWidenT_bnd 2 16 (by norm_num) srcTenthCL0)
    (by rw [g1]; norm_num) 8
  rw [g1] at a1
  rw [a1.2, d1, twColCheck_rat 16 3 8 _ _ _ (by norm_num) a1.1 (by norm_num)
    srcTenthC_check1 _ 32 (by norm_num) (by norm_num),
    ← twWidenT_rat 3 16 (by norm_num) srcTenthCL1 32]
  have a2 := tensorWordAll_actual srcTenthCW2
    (twWidenT_bnd 3 16 (by norm_num) srcTenthCL1)
    (by rw [g2]; norm_num) 32
  rw [g2] at a2
  rw [a2.2, d2, twColCheck_rat 16 4 32 _ _ _ (by norm_num) a2.1 (by norm_num)
    srcTenthC_check2 _ 32 (by norm_num) (by norm_num),
    ← twWidenT_rat 4 20 (by norm_num) srcTenthCL2 32]
  have a3 := tensorWordAll_actual srcTenthCW3
    (twWidenT_bnd 4 20 (by norm_num) srcTenthCL2)
    (by rw [g3]; norm_num) 32
  rw [g3] at a3
  rw [a3.2, d3, twColCheck_rat 20 4 32 _ _ _ (by norm_num) a3.1 (by norm_num)
    srcTenthC_check3 _ 64 (by norm_num) (by norm_num),
    ← twWidenT_rat 4 24 (by norm_num) srcTenthCYLit 64]
  rfl

/-- The incoming Tenth vector with the literal matrix block and the cheap tensor. -/
def srcTenthYC : IdentVec :=
  ⟨srcTenthYMat, ShortData.ofList srcTenthYT, 1 / 16, tensorRat 24 srcTenthYXC 64⟩

/-- The cheap incoming representation is exact. -/
theorem srcTenthYC_actual :
    griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis) = srcTenthYC.real := by
  have hT' : localTensorRepresentation
      (identWordFiber ((srcWordData srcTenthYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal (fifthSrcVecW 24).ten) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 srcTenthYXC 64) := by
    rw [srcWordData_fst]
    exact srcTenthY_tensor_chain
  have h := IdentVec.word_actual (fifthSrcVecW 24) (srcWordData srcTenthYWord) srcTenthY_letters
    srcTenthYD srcTenthY_composite.1 srcTenthY_composite.2.1 srcTenthY_composite.2.2 srcTenthYT
    srcTenthY_short _ hT' _ (fifthSrcW_rep (by norm_num))
  rw [srcWordData_fst] at h
  rw [← srcTenthYWord_local]
  change griessConwayEncode (rhoLocal (identWordLocal srcTenthYWord)
    (generatedAxisGlobalTwelveRepresentative 4)) = _
  rw [h]
  unfold srcTenthYC
  rw [← srcTenthYMat_eq]
  rfl

/-- The short block of the cheap incoming representation satisfies the range conditions. -/
theorem srcTenthYC_ok : srcTenthYC.sh.ok = true := ofList_ok _ srcTenthY_labels

/-- The short scale of the cheap incoming representation. -/
theorem srcTenthYC_sden : srcTenthYC.sden = 1 / 16 := rfl

set_option maxRecDepth 100000 in
/-- The pair terms at short scale `1 / 128`. -/
def srcTenthCPairs : List (ℕ × ℤ) :=
  [(2, 4), (3, -4), (4, -4), (5, 4), (6, -4), (8, 4), (9, 4), (11, 4), (12, -4), (13, -4),
    (14, -4), (17, -4), (18, 4), (19, 4), (21, -4), (23, -4), (29, 4), (32, -4), (37, -4),
    (38, -4), (42, -4), (44, -4), (50, -4), (53, 4), (58, 4), (59, 4), (63, 4), (65, 4),
    (66, -4), (67, 4), (68, -4), (69, -4), (71, 4), (72, 4), (74, -4), (75, -4), (76, -4),
    (77, 4), (80, 4), (81, -4), (82, -4), (84, 4), (86, 4), (87, 4), (88, -4), (90, -4),
    (91, -4), (93, -4), (94, -4), (95, -12), (96, -4), (98, 8), (99, -4), (100, 4), (101, -4),
    (103, 4), (104, -8), (105, 4), (106, 4), (108, 4), (109, -4), (111, -4), (112, -4),
    (113, -4), (114, -4), (117, 4), (118, 4), (119, -4), (121, -4), (123, 4), (125, -4),
    (126, 4), (128, -4), (129, -4), (130, -4), (131, -4), (134, -4), (135, -4), (136, 4),
    (138, 4), (141, -4), (142, -4), (144, -4), (145, 4), (146, 12), (147, -4), (149, -8),
    (150, 4), (151, -4), (152, 4), (154, -4), (155, 8), (158, -4), (163, -4), (164, -4),
    (168, -4), (170, -4), (171, 4), (173, -4), (174, -4), (175, -4), (176, 4), (179, -4),
    (180, 4), (181, 4), (183, -4), (186, 4), (187, -4), (188, -4), (189, -4), (192, 4),
    (193, -4), (194, -4), (196, 4), (202, 4), (203, 4), (207, 4), (209, 4), (210, 4), (211, 4),
    (212, 4), (215, 4), (216, 4), (217, -4), (219, -4), (221, 12), (222, 4), (224, -8),
    (225, -4), (226, 4), (227, -4), (229, 4), (230, 8), (231, 4), (233, -8), (234, 4), (235, -4),
    (236, 4), (238, -4), (239, 8), (242, -4), (243, -4), (244, 4), (246, 4), (248, 4), (252, 4),
    (254, 4), (258, 4), (260, -12), (261, -4), (262, 4), (264, -4), (266, -4), (268, 4),
    (271, -4), (274, 4), (278, 12), (279, 4), (280, 4), (281, -4), (282, 4), (284, -4),
    (285, -4), (287, -4), (288, 4), (289, 4), (290, 4), (293, 4), (294, -4), (295, -4), (297, 4),
    (299, 4), (305, -4), (308, 4), (313, 4), (314, 4), (318, 4), (320, 4), (326, 4), (329, -4),
    (334, -4), (335, -4), (339, -4), (341, -4), (342, 4), (343, -4), (344, 4), (345, 4),
    (347, -4), (348, -4), (350, 4), (351, 4), (352, 4), (353, -4), (356, -4), (357, 4), (358, 4),
    (360, -4), (362, -4), (363, -4), (364, -12), (366, 4), (367, 4), (369, 4), (370, -12),
    (371, -4), (372, 4), (374, 8), (375, 4), (376, -4), (377, 4), (379, -4), (380, -8),
    (381, 12), (382, -4), (384, -4), (385, 4), (387, 4), (388, 4), (389, 4), (390, 4), (393, -4),
    (394, -4), (395, 4), (397, 4), (399, -4), (401, 4), (402, -4), (404, 4), (405, 4), (406, 4),
    (407, 4), (410, 4), (411, 4), (412, -4), (414, -4), (417, 4), (418, 4), (420, 4), (421, 12),
    (422, 4), (423, 4), (425, -8), (426, -4), (427, 4), (428, -4), (430, 4), (431, 8), (434, 4),
    (439, 4), (440, 4), (444, 4), (446, 4), (447, 12), (449, 4), (450, 4), (451, 4), (452, -4),
    (455, 4), (456, -4), (457, -4), (459, 4), (462, -4), (463, 4), (464, 4), (465, 4), (468, -4),
    (469, 4), (470, 4), (472, -4), (478, -4), (479, -4), (483, -4), (485, -4), (486, -4),
    (487, -4), (488, 12), (491, -4), (492, -4), (493, 4), (495, 4), (497, 4), (498, -4),
    (500, -8), (501, 4), (502, -4), (503, 4), (505, -4), (506, 8), (507, -4), (509, -8),
    (510, -4), (511, 4), (512, -4), (514, 4), (515, 8), (518, 4), (519, 4), (520, -4), (522, -4),
    (524, -4), (528, -4), (530, -4), (534, -4), (536, 12), (537, 4), (538, 12), (540, 4),
    (542, 4), (544, 12), (547, 4), (550, -4)]

set_option maxRecDepth 100000 in
/-- The literal pair terms of `tenthSrcVec` are the pair terms at short scale `1 / 128`, rescaled.
-/
theorem srcTenthCPairs_scale : srcTenthPairs = srcTenthCPairs.map (fun q => (q.1, 262144 * q.2)) :=
    by
  decide +kernel

/-- The literal pair terms agree with the triality formula at short scale `1 / 128`. -/
theorem tenthSrcC_pairs : twPairCheck srcTenthCPairs srcTenthYC 64 = true := by
  rw [srcTwPairCheck_congr _ srcTenthYC srcTenthYL 64 rfl rfl rfl,
    ← srcTwPairCheck_scale srcTenthCPairs 262144 srcTenthYL srcTenthYDen 64 (by norm_num)
      (by rw [srcTenthYDen_eq]; norm_num), ← srcTenthCPairs_scale]
  exact tenthSrc_pairs

/-- The literal matrix block agrees with the triality formula. -/
theorem tenthSrcC_mat : twMatCheck srcTenthMat srcTenthYC = true := by
  rw [srcTwMatCheck_congr _ srcTenthYC srcTenthYL rfl rfl rfl]
  exact tenthSrc_mat

/-- The octad list covers the incoming octad blocks. -/
theorem tenthSrcC_octs : twOctCheck srcTenthOcts srcTenthYC = true := by
  rw [srcTwOctCheck_congr _ srcTenthYC srcTenthYL rfl]
  exact tenthSrc_octs

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem tenthSrcC_oddBound :
    srcTenthYC.sh.odd.all (fun q => decide ((8 * q.2).natAbs ≤ 32)) = true ∧
      4 * 15 + srcTenthYC.sh.odd.length * 32 + 60 < 2 ^ 24 := by
  decide +kernel

/-- The triality image of the cheap incoming vector (short scale `1 / 128`). -/
def tenthSrcVecC0 : IdentVec :=
  twTriVec 24 srcTenthYC srcTenthYXC 64 srcTenthMat srcTenthCPairs srcTenthOcts 1 8

/-- The triality image of the cheap incoming vector represents the Tenth axis. -/
theorem tenthSrcC0_actual : griessConwayEncode generatedTenthAxis = tenthSrcVecC0.real := by
  rw [generatedTenthAxis_local_expression]
  exact twTriVec_actual 24 15 32 srcTenthYC srcTenthYXC 64 srcTenthMat srcTenthCPairs srcTenthOcts 1
      8
    srcTenthYC_ok rfl (by norm_num) srcTenthYXC_bnd tenthSrcC_oddBound.1
    (by have := tenthSrcC_oddBound.2; omega)
    (by rw [srcTenthYC_sden]; norm_num) (by rw [srcTenthYC_sden]; norm_num)
    tenthSrcC_mat tenthSrcC_pairs tenthSrcC_octs _ srcTenthYC_actual

/-- The computed packed tensor of the triality image (numerators over `128`). -/
def tenthX12C : List SVec := twTriTen 24 8 srcTenthYXC srcTenthYC.sh.odd

/-- Bounds of the computed packed tensor. -/
theorem tenthX12C_bnd : TBnd 24 (4 * 15 + srcTenthYC.sh.odd.length * 32) tenthX12C :=
  twTriTen_bnd 24 15 32 8 srcTenthYXC srcTenthYC.sh.odd srcTenthYXC_bnd
    (fun q hq => by
      have h := tenthSrcC_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    (by have := tenthSrcC_oddBound.2; omega)

set_option maxRecDepth 100000 in
/-- The computed tensor is four times the compact literal. -/
theorem tenthX12_check : twColCheck 24 4 4 tenthX12C srcTenthCXLit = true := by
  decide +kernel

/-- The Tenth axis with the compact literal tensor block. -/
def tenthSrcVecC (w : ℕ) : IdentVec :=
  ⟨srcTenthMat, tenthSrcVecC0.sh, tenthSrcVecC0.sden, tensorRat w (twWidenT 4 w srcTenthCXLit) 32⟩

/-- The compact tensor block is the computed tensor block. -/
theorem tenthSrcVecC_ten_eq (w : ℕ) (hw : 4 ≤ w) :
    (tenthSrcVecC w).ten = tenthSrcVecC0.ten := by
  change tensorRat w (twWidenT 4 w srcTenthCXLit) 32 = tensorRat 24 tenthX12C (2 * 64)
  rw [twWidenT_rat 4 w hw]
  exact (twColCheck_rat 24 4 4 _ tenthX12C srcTenthCXLit (by norm_num) tenthX12C_bnd
    (by have := tenthSrcC_oddBound.2; omega) tenthX12_check (2 * 64) 32 (by norm_num)
    (by norm_num)).symm

/-- The compact representation has the coordinates of the computed one. -/
theorem tenthSrcVecC_real (w : ℕ) (hw : 4 ≤ w) :
    (tenthSrcVecC w).real = tenthSrcVecC0.real := by
  have ht := tenthSrcVecC_ten_eq w hw
  unfold IdentVec.real IdentVec.packet
  rw [ht]
  rfl

/-- The representation of family representative `11` with the compact tensor. -/
theorem tenthSrcC_rep (w : ℕ) (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 11) =
      (tenthSrcVecC w).real := by
  rw [tenthSrcVecC_real w hw]
  exact tenthSrcC0_actual

/-- The short block of the compact representation satisfies the range conditions. -/
theorem tenthSrcVecC_ok (w : ℕ) : (tenthSrcVecC w).sh.ok = true := by
  change tenthSrcVecC0.sh.ok = true
  exact twTriVec_ok 24 srcTenthYC srcTenthYXC 64 srcTenthMat srcTenthCPairs srcTenthOcts 1 8
    tenthSrcC_pairs tenthSrcC_octs

/-- The short scale of the compact representation. -/
theorem tenthSrcVecC_sden (w : ℕ) : (tenthSrcVecC w).sden = 1 / 128 := by
  change 1 / (2 * (64 : ℚ)) = 1 / 128
  norm_num

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
