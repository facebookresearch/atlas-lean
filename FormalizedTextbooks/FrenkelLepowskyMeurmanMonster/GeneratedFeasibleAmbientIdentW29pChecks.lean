/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W29+ (Twelfth root 29 to Tenth root 48, e = 1)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The source word. -/
def fbW29pH : List IdentLetter := fbW29pHW.map Prod.fst

/-- The target word. -/
def fbW29pG : List IdentLetter := fbW29pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW29pHPlan_word : planWord fbW29pHPlan = fbW29pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW29pHPlan_ok : planOk fbW29pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW29pH_growth : tensorWordGrowthAll fbW29pH * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW29pH_den : tensorWordDenAll fbW29pH = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW29pH_check : fbW29pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW29pHD_cols : ∀ i : Fin 24, qmWordP (fbW29pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW29pHD.colsP i.val, fbW29pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW29pHD_rows : ∀ i : Fin 24,
    fld 24 fbW29pHD.rowsP i.val = rowsOf (fun j => fld 24 fbW29pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW29pGPlan_word : planWord fbW29pGPlan = fbW29pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW29pGPlan_ok : planOk fbW29pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW29pG_growth : tensorWordGrowthAll fbW29pG * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW29pG_den : tensorWordDenAll fbW29pG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW29pG_check : fbW29pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW29pGD_cols : ∀ i : Fin 24, qmWordP (fbW29pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW29pGD.colsP i.val, fbW29pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW29pGD_rows : ∀ i : Fin 24,
    fld 24 fbW29pGD.rowsP i.val = rowsOf (fun j => fld 24 fbW29pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW29pD_ok : fbW29pHD.ok = true ∧ fbW29pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW29pHT_labels : fbW29pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW29pGT_labels : fbW29pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^9`). -/
def fbW29pHX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbW29pHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW29pHX_chk : colsLtB 64 4 fbW29pHX = true ∧
    fbW29pHX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbW29pHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW29pH_tensor : TBnd 64 (2 ^ 4 - 1) fbW29pHX ∧
    localTensorRepresentation (identWordFiber fbW29pH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW29pHX ((tensorWordDenAll fbW29pH : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbW29pHPlan fbW29pHPlan_ok fbt12X64_bnd
    (by rw [fbW29pHPlan_word, fbW29pH_growth]; norm_num) 32
  rw [fbW29pHPlan_word, fbW29pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW29pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbW29pHPlan fbt12X64))
      ((tensorWordDenAll fbW29pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW29pHX_chk.1 fbW29pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^9`). -/
def fbW29pGX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbW29pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW29pGX_chk : colsLtB 64 4 fbW29pGX = true ∧
    fbW29pGX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbW29pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW29pG_tensor : TBnd 64 (2 ^ 4 - 1) fbW29pGX ∧
    localTensorRepresentation (identWordFiber fbW29pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW29pGX ((tensorWordDenAll fbW29pG : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbW29pGPlan fbW29pGPlan_ok t10X64_bnd
    (by rw [fbW29pGPlan_word, fbW29pG_growth]; norm_num) 32
  rw [fbW29pGPlan_word, fbW29pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW29pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbW29pGPlan t10X64))
      ((tensorWordDenAll fbW29pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW29pGX_chk.1 fbW29pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW29pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW29pH, ShortData.ofList fbW29pHT, 1 / 128,
    tensorRat 64 fbW29pHX ((tensorWordDenAll fbW29pH : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the H image. -/
theorem fbW29pL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW29pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW29pL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW29pHW fbW29pH_check fbW29pHD
    fbW29pD_ok.1 fbW29pHD_cols fbW29pHD_rows fbW29pHT fbW29pHT_check _
    fbW29pH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW29pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW29pG, ShortData.ofList fbW29pGT, 1 / 32,
    tensorRat 64 fbW29pGX ((tensorWordDenAll fbW29pG : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the G image. -/
theorem fbW29pW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW29pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW29pW.real :=
  IdentVec.word_actual t10V fbW29pGW fbW29pG_check fbW29pGD
    fbW29pD_ok.2 fbW29pGD_cols fbW29pGD_rows fbW29pGT fbW29pGT_check _
    fbW29pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
