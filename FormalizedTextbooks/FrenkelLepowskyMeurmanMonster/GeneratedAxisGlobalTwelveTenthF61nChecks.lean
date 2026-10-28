/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the Tenth identification T61- (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tf61nH : List IdentLetter := tf61nHW.map Prod.fst

/-- The target word. -/
def tf61nG : List IdentLetter := tf61nGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tf61nHPlan_word : planWord tf61nHPlan = tf61nH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tf61nHPlan_ok : planOk tf61nHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tf61nH_growth : tensorWordGrowthAll tf61nH * 15 = 131941395333120 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tf61nH_den : tensorWordDenAll tf61nH = 2097152 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tf61nH_check : tf61nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tf61nHD_cols : ∀ i : Fin 24, qmWordP (tf61nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tf61nHD.colsP i.val, tf61nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tf61nHD_rows : ∀ i : Fin 24,
    fld 24 tf61nHD.rowsP i.val = rowsOf (fun j => fld 24 tf61nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tf61nGPlan_word : planWord tf61nGPlan = tf61nG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tf61nGPlan_ok : planOk tf61nGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tf61nG_growth : tensorWordGrowthAll tf61nG * 56 = 29360128 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tf61nG_den : tensorWordDenAll tf61nG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tf61nG_check : tf61nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tf61nGD_cols : ∀ i : Fin 24, qmWordP (tf61nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tf61nGD.colsP i.val, tf61nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tf61nGD_rows : ∀ i : Fin 24,
    fld 24 tf61nGD.rowsP i.val = rowsOf (fun j => fld 24 tf61nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tf61nD_ok : tf61nHD.ok = true ∧ tf61nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tf61nHT_labels : tf61nHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tf61nGT_labels : tf61nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^21`). -/
noncomputable def tf61nHX : List SVec := shiftT 21 (canonT 64 (tensorPlanS 64 tf61nHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^5` and is exact. -/
theorem tf61nHX_chk : colsLtB 64 5 tf61nHX = true ∧
    tf61nHX.map (sscale (2 ^ 21)) = canonT 64 (tensorPlanS 64 tf61nHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tf61nH_tensor : TBnd 64 (2 ^ 5 - 1) tf61nHX ∧
    localTensorRepresentation (identWordFiber tf61nH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tf61nHX ((tensorWordDenAll tf61nH : ℚ) * 32 / 2 ^ 21)) := by
  have hP := tensorPlanS_actual tf61nHPlan tf61nHPlan_ok t10X64_bnd
    (by rw [tf61nHPlan_word, tf61nH_growth]; norm_num) 32
  rw [tf61nHPlan_word, tf61nH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tf61nH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 21 5 _ (canonT 64 (tensorPlanS 64 tf61nHPlan t10X64))
      ((tensorWordDenAll tf61nH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tf61nHX_chk.1 tf61nHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^4`). -/
noncomputable def tf61nGX : List SVec := shiftT 4 (canonT 64 (tensorPlanS 64 tf61nGPlan
    (fourthSrcXW 64)))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^3` and is exact. -/
theorem tf61nGX_chk : colsLtB 64 3 tf61nGX = true ∧
    tf61nGX.map (sscale (2 ^ 4)) = canonT 64 (tensorPlanS 64 tf61nGPlan (fourthSrcXW 64)) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tf61nG_tensor : TBnd 64 (2 ^ 3 - 1) tf61nGX ∧
    localTensorRepresentation (identWordFiber tf61nG)
        (generatedAxisGlobalRationalTensorReal (fourthSrcVecW 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tf61nGX ((tensorWordDenAll tf61nG : ℚ) * 1 / 2 ^ 4)) := by
  have hP := tensorPlanS_actual tf61nGPlan tf61nGPlan_ok (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [tf61nGPlan_word, tf61nG_growth]; norm_num) 1
  rw [tf61nGPlan_word, tf61nG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tf61nG : ℚ) * 1)
  have hs := tensorRat_shiftT 64 4 3 _ (canonT 64 (tensorPlanS 64 tf61nGPlan (fourthSrcXW 64)))
      ((tensorWordDenAll tf61nG : ℚ) * 1)
    hc.1 (by norm_num) (by norm_num) tf61nGX_chk.1 tf61nGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fourthSrcVecW_ten, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tf61nL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tf61nH, ShortData.ofList tf61nHT, 1 / 32,
    tensorRat 64 tf61nHX ((tensorWordDenAll tf61nH : ℚ) * 32 / 2 ^ 21)⟩

/-- The coordinates of the H image. -/
theorem tf61nL_actual : griessConwayEncode (rhoLocal (identWordLocal tf61nH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tf61nL.real :=
  IdentVec.word_actual t10V tf61nHW tf61nH_check tf61nHD
    tf61nD_ok.1 tf61nHD_cols tf61nHD_rows tf61nHT tf61nHT_check _
    tf61nH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tf61nW : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet tf61nG, ShortData.ofList tf61nGT, 1 / 8,
    tensorRat 64 tf61nGX ((tensorWordDenAll tf61nG : ℚ) * 1 / 2 ^ 4)⟩

/-- The coordinates of the G image. -/
theorem tf61nW_actual : griessConwayEncode (rhoLocal (identWordLocal tf61nG)
    (generatedAxisGlobalTwelveRepresentative 3)) = tf61nW.real :=
  IdentVec.word_actual (fourthSrcVecW 64) tf61nGW tf61nG_check tf61nGD
    tf61nD_ok.2 tf61nGD_cols tf61nGD_rows tf61nGT tf61nGT_check _
    tf61nG_tensor.2 _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
