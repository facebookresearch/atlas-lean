/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the Tenth identification T11+ (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tv11pH : List IdentLetter := tv11pHW.map Prod.fst

/-- The target word. -/
def tv11pG : List IdentLetter := tv11pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tv11pHPlan_word : planWord tv11pHPlan = tv11pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tv11pHPlan_ok : planOk tv11pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tv11pH_growth : tensorWordGrowthAll tv11pH * 15 = 251658240 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tv11pH_den : tensorWordDenAll tv11pH = 4096 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tv11pH_check : tv11pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tv11pHD_cols : ∀ i : Fin 24, qmWordP (tv11pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv11pHD.colsP i.val, tv11pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tv11pHD_rows : ∀ i : Fin 24,
    fld 24 tv11pHD.rowsP i.val = rowsOf (fun j => fld 24 tv11pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tv11pGPlan_word : planWord tv11pGPlan = tv11pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tv11pGPlan_ok : planOk tv11pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tv11pG_growth : tensorWordGrowthAll tv11pG * 15 = 2013265920 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tv11pG_den : tensorWordDenAll tv11pG = 8192 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tv11pG_check : tv11pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tv11pGD_cols : ∀ i : Fin 24, qmWordP (tv11pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv11pGD.colsP i.val, tv11pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tv11pGD_rows : ∀ i : Fin 24,
    fld 24 tv11pGD.rowsP i.val = rowsOf (fun j => fld 24 tv11pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tv11pD_ok : tv11pHD.ok = true ∧ tv11pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv11pHT_labels : tv11pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv11pGT_labels : tv11pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^12`). -/
def tv11pHX : List SVec := shiftT 12 (canonT 64 (tensorPlanS 64 tv11pHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv11pHX_chk : colsLtB 64 4 tv11pHX = true ∧
    tv11pHX.map (sscale (2 ^ 12)) = canonT 64 (tensorPlanS 64 tv11pHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tv11pH_tensor : TBnd 64 (2 ^ 4 - 1) tv11pHX ∧
    localTensorRepresentation (identWordFiber tv11pH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv11pHX ((tensorWordDenAll tv11pH : ℚ) * 32 / 2 ^ 12)) := by
  have hP := tensorPlanS_actual tv11pHPlan tv11pHPlan_ok t10X64_bnd
    (by rw [tv11pHPlan_word, tv11pH_growth]; norm_num) 32
  rw [tv11pHPlan_word, tv11pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv11pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 12 4 _ (canonT 64 (tensorPlanS 64 tv11pHPlan t10X64))
      ((tensorWordDenAll tv11pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv11pHX_chk.1 tv11pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^13`). -/
def tv11pGX : List SVec := shiftT 13 (canonT 64 (tensorPlanS 64 tv11pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv11pGX_chk : colsLtB 64 4 tv11pGX = true ∧
    tv11pGX.map (sscale (2 ^ 13)) = canonT 64 (tensorPlanS 64 tv11pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tv11pG_tensor : TBnd 64 (2 ^ 4 - 1) tv11pGX ∧
    localTensorRepresentation (identWordFiber tv11pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv11pGX ((tensorWordDenAll tv11pG : ℚ) * 32 / 2 ^ 13)) := by
  have hP := tensorPlanS_actual tv11pGPlan tv11pGPlan_ok t10X64_bnd
    (by rw [tv11pGPlan_word, tv11pG_growth]; norm_num) 32
  rw [tv11pGPlan_word, tv11pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv11pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 13 4 _ (canonT 64 (tensorPlanS 64 tv11pGPlan t10X64))
      ((tensorWordDenAll tv11pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv11pGX_chk.1 tv11pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tv11pL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv11pH, ShortData.ofList tv11pHT, 1 / 32,
    tensorRat 64 tv11pHX ((tensorWordDenAll tv11pH : ℚ) * 32 / 2 ^ 12)⟩

/-- The coordinates of the H image. -/
theorem tv11pL_actual : griessConwayEncode (rhoLocal (identWordLocal tv11pH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv11pL.real :=
  IdentVec.word_actual t10V tv11pHW tv11pH_check tv11pHD
    tv11pD_ok.1 tv11pHD_cols tv11pHD_rows tv11pHT tv11pHT_check _
    tv11pH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tv11pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv11pG, ShortData.ofList tv11pGT, 1 / 32,
    tensorRat 64 tv11pGX ((tensorWordDenAll tv11pG : ℚ) * 32 / 2 ^ 13)⟩

/-- The coordinates of the G image. -/
theorem tv11pW_actual : griessConwayEncode (rhoLocal (identWordLocal tv11pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv11pW.real :=
  IdentVec.word_actual t10V tv11pGW tv11pG_check tv11pGD
    tv11pD_ok.2 tv11pGD_cols tv11pGD_rows tv11pGT tv11pGT_check _
    tv11pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
