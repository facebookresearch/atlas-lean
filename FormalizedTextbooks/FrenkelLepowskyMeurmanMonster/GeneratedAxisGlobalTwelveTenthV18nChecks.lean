/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the Tenth identification T18- (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tv18nH : List IdentLetter := tv18nHW.map Prod.fst

/-- The target word. -/
def tv18nG : List IdentLetter := tv18nGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tv18nHPlan_word : planWord tv18nHPlan = tv18nH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tv18nHPlan_ok : planOk tv18nHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tv18nH_growth : tensorWordGrowthAll tv18nH * 15 = 64424509440 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tv18nH_den : tensorWordDenAll tv18nH = 65536 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tv18nH_check : tv18nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tv18nHD_cols : ∀ i : Fin 24, qmWordP (tv18nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv18nHD.colsP i.val, tv18nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tv18nHD_rows : ∀ i : Fin 24,
    fld 24 tv18nHD.rowsP i.val = rowsOf (fun j => fld 24 tv18nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tv18nGPlan_word : planWord tv18nGPlan = tv18nG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tv18nGPlan_ok : planOk tv18nGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tv18nG_growth : tensorWordGrowthAll tv18nG * 15 = 515396075520 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tv18nG_den : tensorWordDenAll tv18nG = 131072 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tv18nG_check : tv18nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tv18nGD_cols : ∀ i : Fin 24, qmWordP (tv18nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv18nGD.colsP i.val, tv18nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tv18nGD_rows : ∀ i : Fin 24,
    fld 24 tv18nGD.rowsP i.val = rowsOf (fun j => fld 24 tv18nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tv18nD_ok : tv18nHD.ok = true ∧ tv18nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv18nHT_labels : tv18nHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv18nGT_labels : tv18nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^16`). -/
def tv18nHX : List SVec := shiftT 16 (canonT 64 (tensorPlanS 64 tv18nHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv18nHX_chk : colsLtB 64 4 tv18nHX = true ∧
    tv18nHX.map (sscale (2 ^ 16)) = canonT 64 (tensorPlanS 64 tv18nHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tv18nH_tensor : TBnd 64 (2 ^ 4 - 1) tv18nHX ∧
    localTensorRepresentation (identWordFiber tv18nH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv18nHX ((tensorWordDenAll tv18nH : ℚ) * 32 / 2 ^ 16)) := by
  have hP := tensorPlanS_actual tv18nHPlan tv18nHPlan_ok t10X64_bnd
    (by rw [tv18nHPlan_word, tv18nH_growth]; norm_num) 32
  rw [tv18nHPlan_word, tv18nH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv18nH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 16 4 _ (canonT 64 (tensorPlanS 64 tv18nHPlan t10X64))
      ((tensorWordDenAll tv18nH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv18nHX_chk.1 tv18nHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^17`). -/
def tv18nGX : List SVec := shiftT 17 (canonT 64 (tensorPlanS 64 tv18nGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv18nGX_chk : colsLtB 64 4 tv18nGX = true ∧
    tv18nGX.map (sscale (2 ^ 17)) = canonT 64 (tensorPlanS 64 tv18nGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tv18nG_tensor : TBnd 64 (2 ^ 4 - 1) tv18nGX ∧
    localTensorRepresentation (identWordFiber tv18nG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv18nGX ((tensorWordDenAll tv18nG : ℚ) * 32 / 2 ^ 17)) := by
  have hP := tensorPlanS_actual tv18nGPlan tv18nGPlan_ok t10X64_bnd
    (by rw [tv18nGPlan_word, tv18nG_growth]; norm_num) 32
  rw [tv18nGPlan_word, tv18nG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv18nG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 17 4 _ (canonT 64 (tensorPlanS 64 tv18nGPlan t10X64))
      ((tensorWordDenAll tv18nG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv18nGX_chk.1 tv18nGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tv18nL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv18nH, ShortData.ofList tv18nHT, 1 / 32,
    tensorRat 64 tv18nHX ((tensorWordDenAll tv18nH : ℚ) * 32 / 2 ^ 16)⟩

/-- The coordinates of the H image. -/
theorem tv18nL_actual : griessConwayEncode (rhoLocal (identWordLocal tv18nH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv18nL.real :=
  IdentVec.word_actual t10V tv18nHW tv18nH_check tv18nHD
    tv18nD_ok.1 tv18nHD_cols tv18nHD_rows tv18nHT tv18nHT_check _
    tv18nH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tv18nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv18nG, ShortData.ofList tv18nGT, 1 / 32,
    tensorRat 64 tv18nGX ((tensorWordDenAll tv18nG : ℚ) * 32 / 2 ^ 17)⟩

/-- The coordinates of the G image. -/
theorem tv18nW_actual : griessConwayEncode (rhoLocal (identWordLocal tv18nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv18nW.real :=
  IdentVec.word_actual t10V tv18nGW tv18nG_check tv18nGD
    tv18nD_ok.2 tv18nGD_cols tv18nGD_rows tv18nGT tv18nGT_check _
    tv18nG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
