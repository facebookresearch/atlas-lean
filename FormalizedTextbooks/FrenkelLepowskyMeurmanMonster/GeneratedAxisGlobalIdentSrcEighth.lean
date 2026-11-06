/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcEighthWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentTri
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventh

/-! # The Eighth axis as an identification vector

`eighthSrcVecW w : IdentVec` represents the Eighth representative (family representative `7`),
the forward triality image `sExtra (L · v_Odd)` of the original local word image: it is the
generic triality image `twTriVec` (worker `gtwelfth`) of `srcEighthY w`, with the literal image
matrix block and image pair terms checked entrywise in the kernel against the triality formulas,
and the octad label list of the source blocks. `eighthSrcW_rep` binds it to the genuine
coordinates. Densities: 156 nonzero pair terms, 264 octad blocks of `64`
(Fourier images), odd terms read off the packed tensor; dense tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The image matrix block of the Eighth axis. -/
def srcEighthMat : MatRep := ⟨0, [
    ((3 / 8 : ℚ), unitList 0), ((3 / 8 : ℚ), unitList 1), ((3 / 8 : ℚ), unitList 2),
    ((3 / 8 : ℚ), unitList 3), ((1 / 4 : ℚ), unitList 4), ((3 / 8 : ℚ), unitList 5),
    ((3 / 8 : ℚ), unitList 6), ((1 / 4 : ℚ), unitList 7), ((1 / 4 : ℚ), unitList 8),
    ((3 / 8 : ℚ), unitList 9), ((3 / 8 : ℚ), unitList 10), ((1 / 4 : ℚ), unitList 11),
    ((1 / 4 : ℚ), unitList 12), ((1 / 4 : ℚ), unitList 13), ((1 / 4 : ℚ), unitList 14),
    ((1 / 4 : ℚ), unitList 15), ((3 / 8 : ℚ), unitList 16), ((1 / 4 : ℚ), unitList 17),
    ((3 / 8 : ℚ), unitList 18), ((1 / 4 : ℚ), unitList 19), ((3 / 4 : ℚ), unitList 20),
    ((1 / 4 : ℚ), unitList 21), ((3 / 8 : ℚ), unitList 22), ((3 / 8 : ℚ), unitList 23)]⟩

/-- Packed octad labels (10-bit fields) of the Eighth source blocks. -/
@[irreducible] def srcEighthOsPacked : ℕ :=
    0x431043e0f03b0dc360d4340a426094220841e0701b05c1604c120441003c0e0200500800 |||
    (0xfc7e1f47c1ec7a1e4781dc761c4701b46c1a467194631845e1705b1445012c4a12046114 <<< 288) |||
    (0xe350d333cce32cca314c42fcbe2e4b72ccb22a0a6294a32809e250922408e22487204801 <<< 576) |||
    (0x52a491224791d46d164550f4350b41d0541103400ff3f8fc3e4f63d4f23c4ee3a0e7384d <<< 864) |||
    (0x6498d625835fd7a5d9715bd6a5a56859d605755b5615654d4c52d4a525435093f4e5334b <<< 1152) |||
    (0xf07bde9799e1779db755d3745ce721c56fdbd6e9b56c5b06b5ac6a1a66919e6759865995 <<< 1440) |||
    (0x22479023f8fa3d8d6338c22f8962388a2087a1c84a1083a0c81a047f9fd7f1fa7e5f77c5 <<< 1728) |||
    (0x4a8ea0a769ba6692a2e89a1e81a027f9e6789d6749c6709ba6b996649765c946509324b9 <<< 2016) |||
    (0x6ecbaee9b96e1b82dfb7addb72d8b56d1b42cfb3acdb32c8b12c2b02bfaeeb6ad2afaaea <<< 2304) |||
    (0xbd2f2bc6f0bb <<< 2592)

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 0. -/
def srcEighthP0 : List (ℕ × ℤ) := [
    (0, 1024), (1, 1024), (2, 1024), (4, 1024), (5, 1024), (8, 1024), (9, 1024), (15, -1024),
    (17, 1024), (19, -2048), (21, 1024), (22, 1024), (23, 1024), (24, 1024), (26, 1024),
    (27, 1024), (30, 1024), (31, 1024), (37, -1024), (39, 1024), (41, -2048), (43, 1024),
    (44, 1024), (45, 1024), (47, 1024), (48, 1024), (51, 1024), (52, 1024), (58, -1024),
    (60, 1024), (62, -2048), (64, 1024), (65, 1024), (67, 1024), (68, 1024), (71, 1024),
    (72, 1024), (78, -1024), (80, 1024), (82, -2048), (84, 1024), (85, 1024), (105, 1024),
    (108, 1024), (109, 1024), (115, -1024), (117, 1024), (119, -2048), (121, 1024),
    (122, 1024), (125, 1024), (126, 1024), (132, -1024), (134, 1024), (136, -2048),
    (138, 1024), (139, 1024), (171, 1024), (177, -1024), (179, 1024), (181, -2048),
    (183, 1024), (184, 1024), (190, -1024), (192, 1024), (194, -2048), (196, 1024),
    (197, 1024), (249, -1024), (251, 2048), (253, -1024), (254, -1024), (262, -2048),
    (264, 1024), (265, 1024), (271, -2048), (272, -2048), (275, 1024), (276, -1024),
    (277, -1024), (278, -1024), (280, -1024), (281, -1024), (284, -1024), (285, -1024),
    (291, 1024), (293, -1024), (295, 2048), (297, -1024), (298, -1024), (299, -1024),
    (300, -1024)]

set_option maxHeartbeats 2000000 in
-- Elaborating a long literal list of pair terms.
/-- Image pair terms, part 1. -/
def srcEighthP1 : List (ℕ × ℤ) := [
    (302, -1024), (303, -1024), (306, -1024), (307, -1024), (313, 1024), (315, -1024),
    (317, 2048), (319, -1024), (320, -1024), (321, -1024), (323, -1024), (324, -1024),
    (327, -1024), (328, -1024), (334, 1024), (336, -1024), (338, 2048), (340, -1024),
    (341, -1024), (343, -1024), (344, -1024), (347, -1024), (348, -1024), (354, 1024),
    (356, -1024), (358, 2048), (360, -1024), (361, -1024), (381, -1024), (384, -1024),
    (385, -1024), (391, 1024), (393, -1024), (395, 2048), (397, -1024), (398, -1024),
    (401, -1024), (402, -1024), (408, 1024), (410, -1024), (412, 2048), (414, -1024),
    (415, -1024), (447, -1024), (453, 1024), (455, -1024), (457, 2048), (459, -1024),
    (460, -1024), (466, 1024), (468, -1024), (470, 2048), (472, -1024), (473, -1024),
    (525, 1024), (527, -2048), (529, 1024), (530, 1024), (538, 2048), (540, -1024),
    (541, -1024), (547, 2048), (548, 2048), (551, -1024)]

/-- The image pair terms of the Eighth axis (scale `1/8192`). -/
def srcEighthP : List (ℕ × ℤ) := srcEighthP0 ++
  srcEighthP1

/-- The octad labels of the source blocks. -/
def srcEighthOs : List ℕ := srcDecodeOcts srcEighthOsPacked 264

/-- The spatial image `S e₀` of the first unit vector under the Eighth word. -/
def srcEighthE0 : List ℚ := [
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ)]

/-- The literal source matrix block `(1/4) I + 2 (S e₀)(S e₀)ᵀ` of `L · v_Odd`. -/
def srcEighthYMat : MatRep := ⟨1 / 4, [(2, srcEighthE0)]⟩

set_option maxRecDepth 100000 in
/-- The spatial image of `e₀` under the Eighth word. -/
theorem srcEighth_spatial_e0 :
    spWordVec identSpatialAlphabet srcEighthH (unitList 0) = srcEighthE0 := by
  decide +kernel

/-- The source matrix block is the literal one. -/
theorem srcEighthYMat_eq : oddSrcMat.act identSpatialAlphabet srcEighthH = srcEighthYMat := by
  change (⟨1 / 4, [(2, spWordVec identSpatialAlphabet srcEighthH (unitList 0))]⟩ : MatRep) = _
  rw [srcEighth_spatial_e0]
  rfl

/-- The pair terms of `L · v_Odd`, materialized. -/
def srcEighthYPairs : List (ℕ × ℤ) := []

set_option maxRecDepth 100000 in
/-- The materialized pair terms are those of the transported list. -/
theorem srcEighthYPairs_eq : (ShortData.ofList srcEighthT).pairs = srcEighthYPairs := by
  decide +kernel

/-- The short block of `L · v_Odd` with materialized pair terms. -/
def srcEighthYSh : ShortData :=
  ⟨srcEighthYPairs, (ShortData.ofList srcEighthT).oct, (ShortData.ofList srcEighthT).odd⟩

/-- The materialized short block is the transported one. -/
theorem srcEighthYSh_eq : srcEighthYSh = ShortData.ofList srcEighthT := by
  rw [srcEighthYSh, ← srcEighthYPairs_eq]

/-- The identification vector of `L · v_Odd` with literal matrix block and pair terms. -/
def srcEighthYL (w : ℕ) : IdentVec :=
  ⟨srcEighthYMat, srcEighthYSh, 1 / 4,
    tensorRat w (srcEighthYX w) ((tensorWordDenAll srcEighthH : ℚ) * 1)⟩

/-- The literal vector is the word image vector. -/
theorem srcEighthYL_eq (w : ℕ) : srcEighthYL w = srcEighthY w := by
  unfold srcEighthYL srcEighthY
  rw [srcEighthYMat_eq, srcEighthYSh_eq]

/-- The Eighth axis as an identification vector with tensor columns of width `w`. -/
def eighthSrcVecW (w : ℕ) : IdentVec :=
  twTriVec w (srcEighthYL w) (srcEighthYX w) ((tensorWordDenAll srcEighthH : ℚ) * 1)
    srcEighthMat srcEighthP srcEighthOs 256 2048

set_option maxRecDepth 100000 in
/-- The image matrix block is the triality image of the source blocks (width `0` instance). -/
theorem srcEighthMat_check0 : twMatCheck srcEighthMat (srcEighthYL 0) = true := by
  decide +kernel

/-- One entry of the image pair check. -/
def srcEighthPE (s p : ℕ) : Bool :=
  decide (lookupQ srcEighthP (276 * s + p) / (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)) =
    twTriPairEntry (srcEighthYL 0) s p)

set_option maxRecDepth 100000 in
/-- Image pair check entries `0`..`45` of sign `0`. -/
theorem srcEighthPE_0_0 : (List.range' 0 46).all (srcEighthPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `46`..`91` of sign `0`. -/
theorem srcEighthPE_0_46 : (List.range' 46 46).all (srcEighthPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `92`..`137` of sign `0`. -/
theorem srcEighthPE_0_92 : (List.range' 92 46).all (srcEighthPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `138`..`183` of sign `0`. -/
theorem srcEighthPE_0_138 : (List.range' 138 46).all (srcEighthPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `184`..`229` of sign `0`. -/
theorem srcEighthPE_0_184 : (List.range' 184 46).all (srcEighthPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `230`..`275` of sign `0`. -/
theorem srcEighthPE_0_230 : (List.range' 230 46).all (srcEighthPE 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `0`..`45` of sign `1`. -/
theorem srcEighthPE_1_0 : (List.range' 0 46).all (srcEighthPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `46`..`91` of sign `1`. -/
theorem srcEighthPE_1_46 : (List.range' 46 46).all (srcEighthPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `92`..`137` of sign `1`. -/
theorem srcEighthPE_1_92 : (List.range' 92 46).all (srcEighthPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `138`..`183` of sign `1`. -/
theorem srcEighthPE_1_138 : (List.range' 138 46).all (srcEighthPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `184`..`229` of sign `1`. -/
theorem srcEighthPE_1_184 : (List.range' 184 46).all (srcEighthPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Image pair check entries `230`..`275` of sign `1`. -/
theorem srcEighthPE_1_230 : (List.range' 230 46).all (srcEighthPE 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The image pair labels are pair labels. -/
theorem srcEighthP_labels : srcEighthP.all (fun q => decide (q.1 < 552)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- All entries of the image pair check, for one sign. -/
theorem srcEighthPE_all (s : ℕ) (hs : s < 2) : (List.range 276).all (srcEighthPE s) = true := by
  have h : List.range 276 = List.range' 0 46 ++ List.range' 46 46 ++ List.range' 92 46 ++
      List.range' 138 46 ++ List.range' 184 46 ++ List.range' 230 46 := by decide
  rw [h]
  simp only [List.all_append, Bool.and_eq_true]
  interval_cases s
  · exact ⟨⟨⟨⟨⟨srcEighthPE_0_0, srcEighthPE_0_46⟩, srcEighthPE_0_92⟩, srcEighthPE_0_138⟩,
      srcEighthPE_0_184⟩, srcEighthPE_0_230⟩
  · exact ⟨⟨⟨⟨⟨srcEighthPE_1_0, srcEighthPE_1_46⟩, srcEighthPE_1_92⟩, srcEighthPE_1_138⟩,
      srcEighthPE_1_184⟩, srcEighthPE_1_230⟩

/-- The image pair terms are the triality image of the source blocks (width `0` instance). -/
theorem srcEighthP_check0 :
    twPairCheck srcEighthP (srcEighthYL 0) ((tensorWordDenAll srcEighthH : ℚ) * 1) = true := by
  unfold twPairCheck
  rw [srcEighthP_labels, Bool.true_and, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro p _
  have h := srcEighthPE_all s.val s.isLt
  rw [List.all_eq_true] at h
  exact h p.val (List.mem_range.mpr p.isLt)

set_option maxRecDepth 100000 in
/-- The octad label list covers the source blocks (width `0` instance). -/
theorem srcEighthOs_check0 : twOctCheck srcEighthOs (srcEighthYL 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd source terms scaled by `2048` are at most `6144` (width `0` instance). -/
theorem srcEighth_odd_bound0 : (srcEighthYL 0).sh.odd.all
    (fun q => decide (((2048 : ℤ) * q.2).natAbs ≤ 6144)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The source has `288` odd terms (width `0` instance). -/
theorem srcEighth_odd_length0 : (srcEighthYL 0).sh.odd.length = 288 := by
  decide +kernel

/-- The short block of the source does not depend on the width. -/
theorem srcEighthYL_sh (w : ℕ) : (srcEighthYL w).sh = (srcEighthYL 0).sh := rfl

/-- The image matrix block is the triality image of the source blocks. -/
theorem srcEighthMat_check (w : ℕ) : twMatCheck srcEighthMat (srcEighthYL w) = true := by
  rw [srcTwMatCheck_congr _ (srcEighthYL w) (srcEighthYL 0) rfl rfl rfl]
  exact srcEighthMat_check0

/-- The image pair terms are the triality image of the source blocks. -/
theorem srcEighthP_check (w : ℕ) :
    twPairCheck srcEighthP (srcEighthYL w) ((tensorWordDenAll srcEighthH : ℚ) * 1) = true := by
  rw [srcTwPairCheck_congr _ (srcEighthYL w) (srcEighthYL 0) _ rfl rfl rfl]
  exact srcEighthP_check0

/-- The octad label list covers the source blocks. -/
theorem srcEighthOs_check (w : ℕ) : twOctCheck srcEighthOs (srcEighthYL w) = true := by
  rw [srcTwOctCheck_congr _ (srcEighthYL w) (srcEighthYL 0) rfl]
  exact srcEighthOs_check0

/-- The odd source terms scaled by `2048` are at most `6144`. -/
theorem srcEighth_odd_bound (w : ℕ) : (srcEighthYL w).sh.odd.all
    (fun q => decide (((2048 : ℤ) * q.2).natAbs ≤ 6144)) = true := by
  rw [srcEighthYL_sh]
  exact srcEighth_odd_bound0

/-- The source has `288` odd terms. -/
theorem srcEighth_odd_length (w : ℕ) : (srcEighthYL w).sh.odd.length = 288 := by
  rw [srcEighthYL_sh]
  exact srcEighth_odd_length0

/-- The Eighth representative has the coordinates of `eighthSrcVecW w`. -/
theorem eighthSrcW_rep {w : ℕ} (hw : 31 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 7) = (eighthSrcVecW w).real := by
  rw [srcEighth_rep_eq]
  apply twTriVec_actual w (16777216 * 8) 6144 (srcEighthYL w) (srcEighthYX w) _ srcEighthMat
    srcEighthP srcEighthOs 256 2048 (by rw [srcEighthYL_eq]; exact srcEighthY_ok w) rfl
    (by rw [srcEighthH_den]; norm_num) (srcEighthYX_bnd (by omega)) (srcEighth_odd_bound w)
  · rw [srcEighth_odd_length]
    calc 4 * (16777216 * 8) + 288 * 6144 < 2 ^ 31 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  · change ((2048 : ℤ) : ℚ) = 1 / 4 * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))
    rw [srcEighthH_den]
    norm_num
  · change ((256 : ℤ) : ℚ) / (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)) = 1 / 4 / 8
    rw [srcEighthH_den]
    norm_num
  · exact srcEighthMat_check w
  · exact srcEighthP_check w
  · exact srcEighthOs_check w
  · rw [srcEighthYL_eq]
    exact srcEighthY_actual (by omega)

/-- The short block of the Eighth representation satisfies the range conditions. -/
theorem eighthSrcVecW_ok (w : ℕ) : (eighthSrcVecW w).sh.ok = true :=
  twTriVec_ok w _ _ _ _ _ _ _ _ (srcEighthP_check w) (srcEighthOs_check w)

/-- The tensor block of the Eighth representation. -/
theorem eighthSrcVecW_ten (w : ℕ) : (eighthSrcVecW w).ten =
    tensorRat w (twTriTen w 2048 (srcEighthYX w) (srcEighthYL w).sh.odd)
      (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)) := rfl

/-- Bounds of the packed tensor block of the Eighth representation. -/
theorem eighthSrcVecW_bnd {w : ℕ} (hw : 31 ≤ w) :
    TBnd w (4 * (16777216 * 8) + 288 * 6144)
      (twTriTen w 2048 (srcEighthYX w) (srcEighthYL w).sh.odd) := by
  have h := twTriTen_bnd w (16777216 * 8) 6144 2048 (srcEighthYX w) (srcEighthYL w).sh.odd
    (srcEighthYX_bnd (by omega)) (by simpa [List.all_eq_true] using srcEighth_odd_bound w)
    (by rw [srcEighth_odd_length]
        calc 4 * (16777216 * 8) + 288 * 6144 < 2 ^ 31 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw)
  rw [srcEighth_odd_length] at h
  exact h

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
