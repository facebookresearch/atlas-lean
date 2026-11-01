/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcNinthCS

/-! # The Ninth axis as a cheap identification vector

`ninthSrcVecC w : IdentVec` represents the Ninth axis (family representative `8`) with the tensor
block given by the widened compact literal `srcNinthCXLit` (numerators over `32`, field bound `15`
at every width `w ≥ 4`) and short scale `1 / 128`. It is the triality image `twTriVec` of the cheap
incoming vector `srcNinthYC`, whose tensor is the widened checkpoint `srcNinthCYLit`
(`srcNinthY_tensor_chain`); the literal matrix block, the octad labels and the matrix check are
those of `ninthSrcVec`, the pair check is the rescaled one. The computed tensor is replaced by the
literal after one packed comparison (`ninthX12_check`). `ninthSrcC_rep` binds it to the genuine
coordinates (pattern of gtwelfth's `twelfthSrcVecC`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The cheap packed tensor of the incoming vector (numerators over `64`, width `24`). -/
def srcNinthYXC : List SVec := twWidenT 4 24 srcNinthCYLit

/-- Bounds of the cheap incoming tensor. -/
theorem srcNinthYXC_bnd : TBnd 24 15 srcNinthYXC := by
  have h := twWidenT_bnd 4 24 (by norm_num) srcNinthCYLit
  norm_num at h
  exact h

/-- The parts of the source word carry the Fifth tensor to the cheap incoming tensor. -/
theorem srcNinthY_tensor_chain :
    localTensorRepresentation (identWordFiber srcNinthYWord)
        (generatedAxisGlobalRationalTensorReal (tensorRat 40 (fifthSrcXW 40) 1)) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 srcNinthYXC 64) := by
  obtain ⟨d0, g0⟩ := srcNinthC_dens
  rw [srcNinthYWord_parts]
  have a0 := tensorWordAll_actual srcNinthCW0
    (fifthSrcXW_bnd (w := 40) (by norm_num))
    (by rw [g0]; norm_num) 1
  rw [g0] at a0
  rw [a0.2, d0, twColCheck_rat 40 4 1024 _ _ _ (by norm_num) a0.1 (by norm_num)
    srcNinthC_check0 _ 64 (by norm_num) (by norm_num),
    ← twWidenT_rat 4 24 (by norm_num) srcNinthCYLit 64]
  rfl

/-- The incoming Ninth vector with the literal matrix block and the cheap tensor. -/
def srcNinthYC : IdentVec :=
  ⟨srcNinthYMat, ShortData.ofList srcNinthYT, 1 / 16, tensorRat 24 srcNinthYXC 64⟩

/-- The cheap incoming representation is exact. -/
theorem srcNinthYC_actual :
    griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis) =
        srcNinthYC.real := by
  have hT' : localTensorRepresentation
      (identWordFiber ((srcWordData srcNinthYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal (fifthSrcVecW 40).ten) =
      generatedAxisGlobalRationalTensorReal (tensorRat 24 srcNinthYXC 64) := by
    rw [srcWordData_fst]
    exact srcNinthY_tensor_chain
  have h := IdentVec.word_actual (fifthSrcVecW 40) (srcWordData srcNinthYWord) srcNinthY_letters
    srcNinthYD srcNinthY_composite.1 srcNinthY_composite.2.1 srcNinthY_composite.2.2 srcNinthYT
    srcNinthY_short _ hT' _ (fifthSrcW_rep (by norm_num))
  rw [srcWordData_fst] at h
  rw [← srcNinthYWord_local]
  change griessConwayEncode (rhoLocal (identWordLocal srcNinthYWord)
    (generatedAxisGlobalTwelveRepresentative 4)) = _
  rw [h]
  unfold srcNinthYC
  rw [← srcNinthYMat_eq]
  rfl

/-- The short block of the cheap incoming representation satisfies the range conditions. -/
theorem srcNinthYC_ok : srcNinthYC.sh.ok = true := ofList_ok _ srcNinthY_labels

/-- The short scale of the cheap incoming representation. -/
theorem srcNinthYC_sden : srcNinthYC.sden = 1 / 16 := rfl

set_option maxRecDepth 100000 in
/-- The pair terms at short scale `1 / 128`. -/
def srcNinthCPairs : List (ℕ × ℤ) :=
  [(2, 4), (4, 4), (7, 4), (8, -4), (10, -4), (11, 4), (17, 4), (19, 4), (24, 4), (26, 4),
    (29, -4), (30, 4), (32, -4), (33, 4), (37, -16), (39, -4), (41, -4), (45, 4), (46, -16),
    (47, -4), (50, -4), (51, -4), (53, 4), (54, 4), (60, 4), (62, -4), (66, -4), (68, 4),
    (69, 4), (72, -4), (75, -4), (76, -4), (77, -4), (78, -4), (79, 4), (81, 4), (83, -4),
    (84, -4), (85, 4), (86, 4), (89, 4), (90, 4), (92, -4), (93, -4), (99, -4), (101, 4),
    (105, 4), (106, 4), (109, 4), (112, 4), (113, 4), (114, 4), (115, -4), (116, 4), (118, -4),
    (120, 4), (121, -4), (122, 4), (124, -4), (125, 4), (127, 4), (128, -4), (134, 4), (136, 4),
    (140, 4), (141, -4), (143, 4), (144, -4), (150, -4), (152, -4), (154, -16), (157, -4),
    (160, -4), (161, 4), (162, 4), (163, 4), (164, -4), (166, 4), (168, -4), (169, -4), (170, 4),
    (171, -4), (174, -4), (175, 4), (176, 4), (177, -4), (178, 4), (180, 4), (182, -4), (183, 4),
    (184, -4), (185, -4), (186, -4), (192, 4), (194, -4), (199, -4), (200, 4), (201, 4),
    (202, 4), (203, 4), (205, -4), (207, 4), (208, -4), (209, -4), (210, -4), (211, 4), (212, 4),
    (213, -4), (214, -4), (216, -4), (218, 4), (219, 4), (220, 4), (225, 4), (227, -4), (234, 4),
    (236, -4), (242, 4), (244, -4), (249, 4), (251, 4), (255, 4), (257, 4), (261, 4), (263, -4),
    (264, 4), (265, 4), (266, -4), (267, -16), (270, 4), (271, 4), (272, 4), (278, -4),
    (280, -4), (283, -4), (284, 4), (286, 4), (287, -4), (293, -4), (295, -4), (298, -16),
    (300, -4), (302, -4), (305, 4), (306, -4), (308, 4), (309, -4), (315, 4), (317, 4),
    (321, -4), (323, 4), (326, 4), (327, 4), (329, -4), (330, -4), (336, -4), (338, 4), (342, 4),
    (344, -4), (345, -4), (348, 4), (351, 4), (352, 4), (353, 4), (354, 4), (355, -4), (357, -4),
    (359, 4), (360, 4), (361, -4), (362, -4), (365, -4), (366, -4), (368, 4), (369, 4), (375, 4),
    (377, -4), (381, -4), (382, -4), (385, -4), (388, -4), (389, -4), (390, -4), (391, 4),
    (392, -4), (394, 4), (396, -4), (397, 4), (398, -4), (400, 4), (401, -4), (403, -4),
    (404, 4), (409, -16), (410, -4), (412, -4), (416, -4), (417, 4), (419, -4), (420, 4),
    (426, 4), (428, 4), (433, 4), (436, 4), (437, -4), (438, -4), (439, -4), (440, 4), (442, -4),
    (444, 4), (445, 4), (446, -4), (447, 4), (450, 4), (451, -4), (452, -4), (453, 4), (454, -4),
    (456, -4), (458, 4), (459, -4), (460, 4), (461, 4), (462, 4), (463, -16), (468, -4),
    (470, 4), (475, 4), (476, -4), (477, -4), (478, -4), (479, -4), (481, 4), (483, -4),
    (484, 4), (485, 4), (486, 4), (487, -4), (488, -4), (489, 4), (490, 4), (492, 4), (494, -4),
    (495, -4), (496, -4), (501, -4), (503, 4), (507, -16), (510, -4), (512, 4), (518, -4),
    (520, 4), (525, -4), (527, -4), (531, -4), (533, -4), (537, -4), (539, 4), (540, -4),
    (541, -4), (542, 4), (546, -4), (547, -4), (548, -4)]

set_option maxRecDepth 100000 in
/-- The literal pair terms of `ninthSrcVec` are the pair terms at short scale `1 / 128`, rescaled.
-/
theorem srcNinthCPairs_scale : srcNinthPairs = srcNinthCPairs.map (fun q => (q.1, 1024 * q.2)) := by
  decide +kernel

/-- The literal pair terms agree with the triality formula at short scale `1 / 128`. -/
theorem ninthSrcC_pairs : twPairCheck srcNinthCPairs srcNinthYC 64 = true := by
  rw [srcTwPairCheck_congr _ srcNinthYC srcNinthYL 64 rfl rfl rfl,
    ← srcTwPairCheck_scale srcNinthCPairs 1024 srcNinthYL srcNinthYDen 64 (by norm_num)
      (by rw [srcNinthYDen_eq]; norm_num), ← srcNinthCPairs_scale]
  exact ninthSrc_pairs

/-- The literal matrix block agrees with the triality formula. -/
theorem ninthSrcC_mat : twMatCheck srcNinthMat srcNinthYC = true := by
  rw [srcTwMatCheck_congr _ srcNinthYC srcNinthYL rfl rfl rfl]
  exact ninthSrc_mat

/-- The octad list covers the incoming octad blocks. -/
theorem ninthSrcC_octs : twOctCheck srcNinthOcts srcNinthYC = true := by
  rw [srcTwOctCheck_congr _ srcNinthYC srcNinthYL rfl]
  exact ninthSrc_octs

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem ninthSrcC_oddBound :
    srcNinthYC.sh.odd.all (fun q => decide ((8 * q.2).natAbs ≤ 32)) = true ∧
      4 * 15 + srcNinthYC.sh.odd.length * 32 + 60 < 2 ^ 24 := by
  decide +kernel

/-- The triality image of the cheap incoming vector (short scale `1 / 128`). -/
def ninthSrcVecC0 : IdentVec :=
  twTriVec 24 srcNinthYC srcNinthYXC 64 srcNinthMat srcNinthCPairs srcNinthOcts 1 8

/-- The triality image of the cheap incoming vector represents the Ninth axis. -/
theorem ninthSrcC0_actual : griessConwayEncode generatedNinthAxis = ninthSrcVecC0.real := by
  rw [generatedNinthAxis_local_expression]
  exact twTriVec_actual 24 15 32 srcNinthYC srcNinthYXC 64 srcNinthMat srcNinthCPairs srcNinthOcts 1
      8
    srcNinthYC_ok rfl (by norm_num) srcNinthYXC_bnd ninthSrcC_oddBound.1
    (by have := ninthSrcC_oddBound.2; omega)
    (by rw [srcNinthYC_sden]; norm_num) (by rw [srcNinthYC_sden]; norm_num)
    ninthSrcC_mat ninthSrcC_pairs ninthSrcC_octs _ srcNinthYC_actual

/-- The computed packed tensor of the triality image (numerators over `128`). -/
def ninthX12C : List SVec := twTriTen 24 8 srcNinthYXC srcNinthYC.sh.odd

/-- Bounds of the computed packed tensor. -/
theorem ninthX12C_bnd : TBnd 24 (4 * 15 + srcNinthYC.sh.odd.length * 32) ninthX12C :=
  twTriTen_bnd 24 15 32 8 srcNinthYXC srcNinthYC.sh.odd srcNinthYXC_bnd
    (fun q hq => by
      have h := ninthSrcC_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    (by have := ninthSrcC_oddBound.2; omega)

set_option maxRecDepth 100000 in
/-- The computed tensor is four times the compact literal. -/
theorem ninthX12_check : twColCheck 24 4 4 ninthX12C srcNinthCXLit = true := by
  decide +kernel

/-- The Ninth axis with the compact literal tensor block. -/
def ninthSrcVecC (w : ℕ) : IdentVec :=
  ⟨srcNinthMat, ninthSrcVecC0.sh, ninthSrcVecC0.sden, tensorRat w (twWidenT 4 w srcNinthCXLit) 32⟩

/-- The compact tensor block is the computed tensor block. -/
theorem ninthSrcVecC_ten_eq (w : ℕ) (hw : 4 ≤ w) :
    (ninthSrcVecC w).ten = ninthSrcVecC0.ten := by
  change tensorRat w (twWidenT 4 w srcNinthCXLit) 32 = tensorRat 24 ninthX12C (2 * 64)
  rw [twWidenT_rat 4 w hw]
  exact (twColCheck_rat 24 4 4 _ ninthX12C srcNinthCXLit (by norm_num) ninthX12C_bnd
    (by have := ninthSrcC_oddBound.2; omega) ninthX12_check (2 * 64) 32 (by norm_num)
    (by norm_num)).symm

/-- The compact representation has the coordinates of the computed one. -/
theorem ninthSrcVecC_real (w : ℕ) (hw : 4 ≤ w) :
    (ninthSrcVecC w).real = ninthSrcVecC0.real := by
  have ht := ninthSrcVecC_ten_eq w hw
  unfold IdentVec.real IdentVec.packet
  rw [ht]
  rfl

/-- The representation of family representative `8` with the compact tensor. -/
theorem ninthSrcC_rep (w : ℕ) (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 8) =
      (ninthSrcVecC w).real := by
  rw [ninthSrcVecC_real w hw]
  exact ninthSrcC0_actual

/-- The short block of the compact representation satisfies the range conditions. -/
theorem ninthSrcVecC_ok (w : ℕ) : (ninthSrcVecC w).sh.ok = true := by
  change ninthSrcVecC0.sh.ok = true
  exact twTriVec_ok 24 srcNinthYC srcNinthYXC 64 srcNinthMat srcNinthCPairs srcNinthOcts 1 8
    ninthSrcC_pairs ninthSrcC_octs

/-- The short scale of the compact representation. -/
theorem ninthSrcVecC_sden (w : ℕ) : (ninthSrcVecC w).sden = 1 / 128 := by
  change 1 / (2 * (64 : ℚ)) = 1 / 128
  norm_num

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
