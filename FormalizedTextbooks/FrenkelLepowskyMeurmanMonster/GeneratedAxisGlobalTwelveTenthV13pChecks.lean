/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV13pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV13pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the Tenth identification T13+ (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tv13pH : List IdentLetter := tv13pHW.map Prod.fst

/-- The target word. -/
def tv13pG : List IdentLetter := tv13pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tv13pHPlan_word : planWord tv13pHPlan = tv13pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tv13pHPlan_ok : planOk tv13pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tv13pH_growth : tensorWordGrowthAll tv13pH * 15 = 251658240 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tv13pH_den : tensorWordDenAll tv13pH = 4096 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tv13pH_check : tv13pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tv13pHD_cols : ∀ i : Fin 24, qmWordP (tv13pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv13pHD.colsP i.val, tv13pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tv13pHD_rows : ∀ i : Fin 24,
    fld 24 tv13pHD.rowsP i.val = rowsOf (fun j => fld 24 tv13pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tv13pGPlan_word : planWord tv13pGPlan = tv13pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tv13pGPlan_ok : planOk tv13pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tv13pG_growth : tensorWordGrowthAll tv13pG * 15 = 515396075520 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tv13pG_den : tensorWordDenAll tv13pG = 131072 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tv13pG_check : tv13pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tv13pGD_cols : ∀ i : Fin 24, qmWordP (tv13pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv13pGD.colsP i.val, tv13pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tv13pGD_rows : ∀ i : Fin 24,
    fld 24 tv13pGD.rowsP i.val = rowsOf (fun j => fld 24 tv13pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tv13pD_ok : tv13pHD.ok = true ∧ tv13pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv13pHT_labels : tv13pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv13pGT_labels : tv13pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^12`). -/
def tv13pHX : List SVec := shiftT 12 (canonT 64 (tensorPlanS 64 tv13pHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv13pHX_chk : colsLtB 64 4 tv13pHX = true ∧
    tv13pHX.map (sscale (2 ^ 12)) = canonT 64 (tensorPlanS 64 tv13pHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tv13pH_tensor : TBnd 64 (2 ^ 4 - 1) tv13pHX ∧
    localTensorRepresentation (identWordFiber tv13pH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv13pHX ((tensorWordDenAll tv13pH : ℚ) * 32 / 2 ^ 12)) := by
  have hP := tensorPlanS_actual tv13pHPlan tv13pHPlan_ok t10X64_bnd
    (by rw [tv13pHPlan_word, tv13pH_growth]; norm_num) 32
  rw [tv13pHPlan_word, tv13pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv13pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 12 4 _ (canonT 64 (tensorPlanS 64 tv13pHPlan t10X64))
      ((tensorWordDenAll tv13pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv13pHX_chk.1 tv13pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^17`). -/
def tv13pGX : List SVec := shiftT 17 (canonT 64 (tensorPlanS 64 tv13pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv13pGX_chk : colsLtB 64 4 tv13pGX = true ∧
    tv13pGX.map (sscale (2 ^ 17)) = canonT 64 (tensorPlanS 64 tv13pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tv13pG_tensor : TBnd 64 (2 ^ 4 - 1) tv13pGX ∧
    localTensorRepresentation (identWordFiber tv13pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv13pGX ((tensorWordDenAll tv13pG : ℚ) * 32 / 2 ^ 17)) := by
  have hP := tensorPlanS_actual tv13pGPlan tv13pGPlan_ok t10X64_bnd
    (by rw [tv13pGPlan_word, tv13pG_growth]; norm_num) 32
  rw [tv13pGPlan_word, tv13pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv13pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 17 4 _ (canonT 64 (tensorPlanS 64 tv13pGPlan t10X64))
      ((tensorWordDenAll tv13pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv13pGX_chk.1 tv13pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tv13pL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv13pH, ShortData.ofList tv13pHT, 1 / 32,
    tensorRat 64 tv13pHX ((tensorWordDenAll tv13pH : ℚ) * 32 / 2 ^ 12)⟩

/-- The coordinates of the H image. -/
theorem tv13pL_actual : griessConwayEncode (rhoLocal (identWordLocal tv13pH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv13pL.real :=
  IdentVec.word_actual t10V tv13pHW tv13pH_check tv13pHD
    tv13pD_ok.1 tv13pHD_cols tv13pHD_rows tv13pHT tv13pHT_check _
    tv13pH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tv13pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv13pG, ShortData.ofList tv13pGT, 1 / 32,
    tensorRat 64 tv13pGX ((tensorWordDenAll tv13pG : ℚ) * 32 / 2 ^ 17)⟩

/-- The coordinates of the G image. -/
theorem tv13pW_actual : griessConwayEncode (rhoLocal (identWordLocal tv13pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv13pW.real :=
  IdentVec.word_actual t10V tv13pGW tv13pG_check tv13pGD
    tv13pD_ok.2 tv13pGD_cols tv13pGD_rows tv13pGT tv13pGT_check _
    tv13pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
