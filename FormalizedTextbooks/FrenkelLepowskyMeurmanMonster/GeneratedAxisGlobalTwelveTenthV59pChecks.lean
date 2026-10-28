/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcS

/-! # Checks of the Tenth identification T59+ (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tv59pH : List IdentLetter := tv59pHW.map Prod.fst

/-- The target word. -/
def tv59pG : List IdentLetter := tv59pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tv59pHPlan_word : planWord tv59pHPlan = tv59pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tv59pHPlan_ok : planOk tv59pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tv59pH_growth : tensorWordGrowthAll tv59pH * 15 = 251658240 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tv59pH_den : tensorWordDenAll tv59pH = 4096 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tv59pH_check : tv59pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tv59pHD_cols : ∀ i : Fin 24, qmWordP (tv59pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv59pHD.colsP i.val, tv59pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tv59pHD_rows : ∀ i : Fin 24,
    fld 24 tv59pHD.rowsP i.val = rowsOf (fun j => fld 24 tv59pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tv59pGPlan_word : planWord tv59pGPlan = tv59pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tv59pGPlan_ok : planOk tv59pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tv59pG_growth : tensorWordGrowthAll tv59pG * 15 = 2013265920 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tv59pG_den : tensorWordDenAll tv59pG = 8192 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tv59pG_check : tv59pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tv59pGD_cols : ∀ i : Fin 24, qmWordP (tv59pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tv59pGD.colsP i.val, tv59pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tv59pGD_rows : ∀ i : Fin 24,
    fld 24 tv59pGD.rowsP i.val = rowsOf (fun j => fld 24 tv59pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tv59pD_ok : tv59pHD.ok = true ∧ tv59pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv59pHT_labels : tv59pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tv59pGT_labels : tv59pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^12`). -/
def tv59pHX : List SVec := shiftT 12 (canonT 64 (tensorPlanS 64 tv59pHPlan (tenthSrcXL 64)))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv59pHX_chk : colsLtB 64 4 tv59pHX = true ∧
    tv59pHX.map (sscale (2 ^ 12)) = canonT 64 (tensorPlanS 64 tv59pHPlan (tenthSrcXL 64)) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tv59pH_tensor : TBnd 64 (2 ^ 4 - 1) tv59pHX ∧
    localTensorRepresentation (identWordFiber tv59pH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv59pHX ((tensorWordDenAll tv59pH : ℚ) * 32 / 2 ^ 12)) := by
  have hP := tensorPlanS_actual tv59pHPlan tv59pHPlan_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [tv59pHPlan_word, tv59pH_growth]; norm_num) 32
  rw [tv59pHPlan_word, tv59pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv59pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 12 4 _ (canonT 64 (tensorPlanS 64 tv59pHPlan (tenthSrcXL 64)))
      ((tensorWordDenAll tv59pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv59pHX_chk.1 tv59pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^13`). -/
def tv59pGX : List SVec := shiftT 13 (canonT 64 (tensorPlanS 64 tv59pGPlan (tenthSrcXL 64)))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tv59pGX_chk : colsLtB 64 4 tv59pGX = true ∧
    tv59pGX.map (sscale (2 ^ 13)) = canonT 64 (tensorPlanS 64 tv59pGPlan (tenthSrcXL 64)) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tv59pG_tensor : TBnd 64 (2 ^ 4 - 1) tv59pGX ∧
    localTensorRepresentation (identWordFiber tv59pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tv59pGX ((tensorWordDenAll tv59pG : ℚ) * 32 / 2 ^ 13)) := by
  have hP := tensorPlanS_actual tv59pGPlan tv59pGPlan_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [tv59pGPlan_word, tv59pG_growth]; norm_num) 32
  rw [tv59pGPlan_word, tv59pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tv59pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 13 4 _ (canonT 64 (tensorPlanS 64 tv59pGPlan (tenthSrcXL 64)))
      ((tensorWordDenAll tv59pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tv59pGX_chk.1 tv59pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tv59pL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv59pH, ShortData.ofList tv59pHT, 1 / 32,
    tensorRat 64 tv59pHX ((tensorWordDenAll tv59pH : ℚ) * 32 / 2 ^ 12)⟩

/-- The coordinates of the H image. -/
theorem tv59pL_actual : griessConwayEncode (rhoLocal (identWordLocal tv59pH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv59pL.real :=
  IdentVec.word_actual t10V tv59pHW tv59pH_check tv59pHD
    tv59pD_ok.1 tv59pHD_cols tv59pHD_rows tv59pHT tv59pHT_check _
    tv59pH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tv59pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tv59pG, ShortData.ofList tv59pGT, 1 / 32,
    tensorRat 64 tv59pGX ((tensorWordDenAll tv59pG : ℚ) * 32 / 2 ^ 13)⟩

/-- The coordinates of the G image. -/
theorem tv59pW_actual : griessConwayEncode (rhoLocal (identWordLocal tv59pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = tv59pW.real :=
  IdentVec.word_actual t10V tv59pGW tv59pG_check tv59pGD
    tv59pD_ok.2 tv59pGD_cols tv59pGD_rows tv59pGT tv59pGT_check _
    tv59pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
