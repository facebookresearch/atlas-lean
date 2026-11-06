/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W16+ (Twelfth root 16 to Tenth root 28, e = 1)

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
def fbW16pH : List IdentLetter := fbW16pHW.map Prod.fst

/-- The target word. -/
def fbW16pG : List IdentLetter := fbW16pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW16pHPlan_word : planWord fbW16pHPlan = fbW16pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW16pHPlan_ok : planOk fbW16pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW16pH_growth : tensorWordGrowthAll fbW16pH * 15 = 983040 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW16pH_den : tensorWordDenAll fbW16pH = 256 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW16pH_check : fbW16pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW16pHD_cols : ∀ i : Fin 24, qmWordP (fbW16pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW16pHD.colsP i.val, fbW16pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW16pHD_rows : ∀ i : Fin 24,
    fld 24 fbW16pHD.rowsP i.val = rowsOf (fun j => fld 24 fbW16pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW16pGPlan_word : planWord fbW16pGPlan = fbW16pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW16pGPlan_ok : planOk fbW16pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW16pG_growth : tensorWordGrowthAll fbW16pG * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW16pG_den : tensorWordDenAll fbW16pG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW16pG_check : fbW16pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW16pGD_cols : ∀ i : Fin 24, qmWordP (fbW16pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW16pGD.colsP i.val, fbW16pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW16pGD_rows : ∀ i : Fin 24,
    fld 24 fbW16pGD.rowsP i.val = rowsOf (fun j => fld 24 fbW16pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW16pD_ok : fbW16pHD.ok = true ∧ fbW16pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW16pHT_labels : fbW16pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW16pGT_labels : fbW16pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^8`). -/
def fbW16pHX : List SVec := shiftT 8 (canonT 64 (tensorPlanS 64 fbW16pHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW16pHX_chk : colsLtB 64 4 fbW16pHX = true ∧
    fbW16pHX.map (sscale (2 ^ 8)) = canonT 64 (tensorPlanS 64 fbW16pHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW16pH_tensor : TBnd 64 (2 ^ 4 - 1) fbW16pHX ∧
    localTensorRepresentation (identWordFiber fbW16pH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW16pHX ((tensorWordDenAll fbW16pH : ℚ) * 32 / 2 ^ 8)) := by
  have hP := tensorPlanS_actual fbW16pHPlan fbW16pHPlan_ok fbt12X64_bnd
    (by rw [fbW16pHPlan_word, fbW16pH_growth]; norm_num) 32
  rw [fbW16pHPlan_word, fbW16pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW16pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 8 4 _ (canonT 64 (tensorPlanS 64 fbW16pHPlan fbt12X64))
      ((tensorWordDenAll fbW16pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW16pHX_chk.1 fbW16pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^9`). -/
def fbW16pGX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbW16pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW16pGX_chk : colsLtB 64 4 fbW16pGX = true ∧
    fbW16pGX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbW16pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW16pG_tensor : TBnd 64 (2 ^ 4 - 1) fbW16pGX ∧
    localTensorRepresentation (identWordFiber fbW16pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW16pGX ((tensorWordDenAll fbW16pG : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbW16pGPlan fbW16pGPlan_ok t10X64_bnd
    (by rw [fbW16pGPlan_word, fbW16pG_growth]; norm_num) 32
  rw [fbW16pGPlan_word, fbW16pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW16pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbW16pGPlan t10X64))
      ((tensorWordDenAll fbW16pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW16pGX_chk.1 fbW16pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW16pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW16pH, ShortData.ofList fbW16pHT, 1 / 128,
    tensorRat 64 fbW16pHX ((tensorWordDenAll fbW16pH : ℚ) * 32 / 2 ^ 8)⟩

/-- The coordinates of the H image. -/
theorem fbW16pL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW16pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW16pL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW16pHW fbW16pH_check fbW16pHD
    fbW16pD_ok.1 fbW16pHD_cols fbW16pHD_rows fbW16pHT fbW16pHT_check _
    fbW16pH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW16pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW16pG, ShortData.ofList fbW16pGT, 1 / 32,
    tensorRat 64 fbW16pGX ((tensorWordDenAll fbW16pG : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the G image. -/
theorem fbW16pW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW16pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW16pW.real :=
  IdentVec.word_actual t10V fbW16pGW fbW16pG_check fbW16pGD
    fbW16pD_ok.2 fbW16pGD_cols fbW16pGD_rows fbW16pGT fbW16pGT_check _
    fbW16pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
