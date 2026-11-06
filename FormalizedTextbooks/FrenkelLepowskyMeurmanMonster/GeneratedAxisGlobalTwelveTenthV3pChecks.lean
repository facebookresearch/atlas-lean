/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the Tenth identification T3+ (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tv3pH : List IdentLetter := tv3pHW.map Prod.fst

/-- The target word. -/
def tv3pG : List IdentLetter := tv3pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tv3pHPlan_word : planWord tv3pHPlan = tv3pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tv3pHPlan_ok : planOk tv3pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tv3pH_growth : tensorWordGrowthAll tv3pH * 15 = 64424509440 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tv3pH_den : tensorWordDenAll tv3pH = 65536 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tv3pH_check : tv3pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tv3pHD_cols : ∀ i : Fin 24, qmWordP (tv3pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv3pHD.colsP i.val, tv3pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tv3pHD_rows : ∀ i : Fin 24,
    fld 24 tv3pHD.rowsP i.val = rowsOf (fun j => fld 24 tv3pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tv3pGPlan_word : planWord tv3pGPlan = tv3pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tv3pGPlan_ok : planOk tv3pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tv3pG_growth : tensorWordGrowthAll tv3pG * 15 = 515396075520 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tv3pG_den : tensorWordDenAll tv3pG = 131072 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tv3pG_check : tv3pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tv3pGD_cols : ∀ i : Fin 24, qmWordP (tv3pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv3pGD.colsP i.val, tv3pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tv3pGD_rows : ∀ i : Fin 24,
    fld 24 tv3pGD.rowsP i.val = rowsOf (fun j => fld 24 tv3pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tv3pD_ok : tv3pHD.ok = true ∧ tv3pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv3pHT_labels : tv3pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv3pGT_labels : tv3pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^16`). -/
def tv3pHX : List SVec := shiftT 16 (canonT 64 (tensorPlanS 64 tv3pHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv3pHX_chk : colsLtB 64 4 tv3pHX = true ∧
    tv3pHX.map (sscale (2 ^ 16)) = canonT 64 (tensorPlanS 64 tv3pHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tv3pH_tensor : TBnd 64 (2 ^ 4 - 1) tv3pHX ∧
    localTensorRepresentation (identWordFiber tv3pH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv3pHX ((tensorWordDenAll tv3pH : ℚ) * 32 / 2 ^ 16)) := by
  have hP := tensorPlanS_actual tv3pHPlan tv3pHPlan_ok t10X64_bnd
    (by rw [tv3pHPlan_word, tv3pH_growth]; norm_num) 32
  rw [tv3pHPlan_word, tv3pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv3pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 16 4 _ (canonT 64 (tensorPlanS 64 tv3pHPlan t10X64))
      ((tensorWordDenAll tv3pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv3pHX_chk.1 tv3pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^17`). -/
def tv3pGX : List SVec := shiftT 17 (canonT 64 (tensorPlanS 64 tv3pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv3pGX_chk : colsLtB 64 4 tv3pGX = true ∧
    tv3pGX.map (sscale (2 ^ 17)) = canonT 64 (tensorPlanS 64 tv3pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tv3pG_tensor : TBnd 64 (2 ^ 4 - 1) tv3pGX ∧
    localTensorRepresentation (identWordFiber tv3pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv3pGX ((tensorWordDenAll tv3pG : ℚ) * 32 / 2 ^ 17)) := by
  have hP := tensorPlanS_actual tv3pGPlan tv3pGPlan_ok t10X64_bnd
    (by rw [tv3pGPlan_word, tv3pG_growth]; norm_num) 32
  rw [tv3pGPlan_word, tv3pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv3pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 17 4 _ (canonT 64 (tensorPlanS 64 tv3pGPlan t10X64))
      ((tensorWordDenAll tv3pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv3pGX_chk.1 tv3pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tv3pL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv3pH, ShortData.ofList tv3pHT, 1 / 32,
    tensorRat 64 tv3pHX ((tensorWordDenAll tv3pH : ℚ) * 32 / 2 ^ 16)⟩

/-- The coordinates of the H image. -/
theorem tv3pL_actual : griessConwayEncode (rhoLocal (identWordLocal tv3pH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv3pL.real :=
  IdentVec.word_actual t10V tv3pHW tv3pH_check tv3pHD
    tv3pD_ok.1 tv3pHD_cols tv3pHD_rows tv3pHT tv3pHT_check _
    tv3pH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tv3pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv3pG, ShortData.ofList tv3pGT, 1 / 32,
    tensorRat 64 tv3pGX ((tensorWordDenAll tv3pG : ℚ) * 32 / 2 ^ 17)⟩

/-- The coordinates of the G image. -/
theorem tv3pW_actual : griessConwayEncode (rhoLocal (identWordLocal tv3pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv3pW.real :=
  IdentVec.word_actual t10V tv3pGW tv3pG_check tv3pGD
    tv3pD_ok.2 tv3pGD_cols tv3pGD_rows tv3pGT tv3pGT_check _
    tv3pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
