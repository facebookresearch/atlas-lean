/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the Tenth identification T22+ (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tv22pH : List IdentLetter := tv22pHW.map Prod.fst

/-- The target word. -/
def tv22pG : List IdentLetter := tv22pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tv22pHPlan_word : planWord tv22pHPlan = tv22pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tv22pHPlan_ok : planOk tv22pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tv22pH_growth : tensorWordGrowthAll tv22pH * 15 = 515396075520 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tv22pH_den : tensorWordDenAll tv22pH = 131072 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tv22pH_check : tv22pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tv22pHD_cols : ∀ i : Fin 24, qmWordP (tv22pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv22pHD.colsP i.val, tv22pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tv22pHD_rows : ∀ i : Fin 24,
    fld 24 tv22pHD.rowsP i.val = rowsOf (fun j => fld 24 tv22pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tv22pGPlan_word : planWord tv22pGPlan = tv22pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tv22pGPlan_ok : planOk tv22pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tv22pG_growth : tensorWordGrowthAll tv22pG * 15 = 4123168604160 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tv22pG_den : tensorWordDenAll tv22pG = 262144 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tv22pG_check : tv22pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tv22pGD_cols : ∀ i : Fin 24, qmWordP (tv22pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv22pGD.colsP i.val, tv22pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tv22pGD_rows : ∀ i : Fin 24,
    fld 24 tv22pGD.rowsP i.val = rowsOf (fun j => fld 24 tv22pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tv22pD_ok : tv22pHD.ok = true ∧ tv22pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv22pHT_labels : tv22pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv22pGT_labels : tv22pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^17`). -/
def tv22pHX : List SVec := shiftT 17 (canonT 64 (tensorPlanS 64 tv22pHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv22pHX_chk : colsLtB 64 4 tv22pHX = true ∧
    tv22pHX.map (sscale (2 ^ 17)) = canonT 64 (tensorPlanS 64 tv22pHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tv22pH_tensor : TBnd 64 (2 ^ 4 - 1) tv22pHX ∧
    localTensorRepresentation (identWordFiber tv22pH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv22pHX ((tensorWordDenAll tv22pH : ℚ) * 32 / 2 ^ 17)) := by
  have hP := tensorPlanS_actual tv22pHPlan tv22pHPlan_ok t10X64_bnd
    (by rw [tv22pHPlan_word, tv22pH_growth]; norm_num) 32
  rw [tv22pHPlan_word, tv22pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv22pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 17 4 _ (canonT 64 (tensorPlanS 64 tv22pHPlan t10X64))
      ((tensorWordDenAll tv22pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv22pHX_chk.1 tv22pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^18`). -/
def tv22pGX : List SVec := shiftT 18 (canonT 64 (tensorPlanS 64 tv22pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv22pGX_chk : colsLtB 64 4 tv22pGX = true ∧
    tv22pGX.map (sscale (2 ^ 18)) = canonT 64 (tensorPlanS 64 tv22pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tv22pG_tensor : TBnd 64 (2 ^ 4 - 1) tv22pGX ∧
    localTensorRepresentation (identWordFiber tv22pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv22pGX ((tensorWordDenAll tv22pG : ℚ) * 32 / 2 ^ 18)) := by
  have hP := tensorPlanS_actual tv22pGPlan tv22pGPlan_ok t10X64_bnd
    (by rw [tv22pGPlan_word, tv22pG_growth]; norm_num) 32
  rw [tv22pGPlan_word, tv22pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv22pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 18 4 _ (canonT 64 (tensorPlanS 64 tv22pGPlan t10X64))
      ((tensorWordDenAll tv22pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv22pGX_chk.1 tv22pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tv22pL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv22pH, ShortData.ofList tv22pHT, 1 / 32,
    tensorRat 64 tv22pHX ((tensorWordDenAll tv22pH : ℚ) * 32 / 2 ^ 17)⟩

/-- The coordinates of the H image. -/
theorem tv22pL_actual : griessConwayEncode (rhoLocal (identWordLocal tv22pH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv22pL.real :=
  IdentVec.word_actual t10V tv22pHW tv22pH_check tv22pHD
    tv22pD_ok.1 tv22pHD_cols tv22pHD_rows tv22pHT tv22pHT_check _
    tv22pH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tv22pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv22pG, ShortData.ofList tv22pGT, 1 / 32,
    tensorRat 64 tv22pGX ((tensorWordDenAll tv22pG : ℚ) * 32 / 2 ^ 18)⟩

/-- The coordinates of the G image. -/
theorem tv22pW_actual : griessConwayEncode (rhoLocal (identWordLocal tv22pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv22pW.real :=
  IdentVec.word_actual t10V tv22pGW tv22pG_check tv22pGD
    tv22pD_ok.2 tv22pGD_cols tv22pGD_rows tv22pGT tv22pGT_check _
    tv22pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
