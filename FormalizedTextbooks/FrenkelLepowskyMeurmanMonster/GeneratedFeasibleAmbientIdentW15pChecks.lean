/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W15+ (Twelfth root 15 to Tenth root 38, e = 1)

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
def fbW15pH : List IdentLetter := fbW15pHW.map Prod.fst

/-- The target word. -/
def fbW15pG : List IdentLetter := fbW15pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW15pHPlan_word : planWord fbW15pHPlan = fbW15pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW15pHPlan_ok : planOk fbW15pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW15pH_growth : tensorWordGrowthAll fbW15pH * 15 = 983040 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW15pH_den : tensorWordDenAll fbW15pH = 256 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW15pH_check : fbW15pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW15pHD_cols : ∀ i : Fin 24, qmWordP (fbW15pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW15pHD.colsP i.val, fbW15pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW15pHD_rows : ∀ i : Fin 24,
    fld 24 fbW15pHD.rowsP i.val = rowsOf (fun j => fld 24 fbW15pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW15pGPlan_word : planWord fbW15pGPlan = fbW15pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW15pGPlan_ok : planOk fbW15pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW15pG_growth : tensorWordGrowthAll fbW15pG * 15 = 2013265920 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW15pG_den : tensorWordDenAll fbW15pG = 8192 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW15pG_check : fbW15pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW15pGD_cols : ∀ i : Fin 24, qmWordP (fbW15pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW15pGD.colsP i.val, fbW15pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW15pGD_rows : ∀ i : Fin 24,
    fld 24 fbW15pGD.rowsP i.val = rowsOf (fun j => fld 24 fbW15pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW15pD_ok : fbW15pHD.ok = true ∧ fbW15pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW15pHT_labels : fbW15pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW15pGT_labels : fbW15pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^8`). -/
def fbW15pHX : List SVec := shiftT 8 (canonT 64 (tensorPlanS 64 fbW15pHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^3` and is exact. -/
theorem fbW15pHX_chk : colsLtB 64 3 fbW15pHX = true ∧
    fbW15pHX.map (sscale (2 ^ 8)) = canonT 64 (tensorPlanS 64 fbW15pHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW15pH_tensor : TBnd 64 (2 ^ 3 - 1) fbW15pHX ∧
    localTensorRepresentation (identWordFiber fbW15pH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW15pHX ((tensorWordDenAll fbW15pH : ℚ) * 32 / 2 ^ 8)) := by
  have hP := tensorPlanS_actual fbW15pHPlan fbW15pHPlan_ok fbt12X64_bnd
    (by rw [fbW15pHPlan_word, fbW15pH_growth]; norm_num) 32
  rw [fbW15pHPlan_word, fbW15pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW15pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 8 3 _ (canonT 64 (tensorPlanS 64 fbW15pHPlan fbt12X64))
      ((tensorWordDenAll fbW15pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW15pHX_chk.1 fbW15pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^13`). -/
def fbW15pGX : List SVec := shiftT 13 (canonT 64 (tensorPlanS 64 fbW15pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^3` and is exact. -/
theorem fbW15pGX_chk : colsLtB 64 3 fbW15pGX = true ∧
    fbW15pGX.map (sscale (2 ^ 13)) = canonT 64 (tensorPlanS 64 fbW15pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW15pG_tensor : TBnd 64 (2 ^ 3 - 1) fbW15pGX ∧
    localTensorRepresentation (identWordFiber fbW15pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW15pGX ((tensorWordDenAll fbW15pG : ℚ) * 32 / 2 ^ 13)) := by
  have hP := tensorPlanS_actual fbW15pGPlan fbW15pGPlan_ok t10X64_bnd
    (by rw [fbW15pGPlan_word, fbW15pG_growth]; norm_num) 32
  rw [fbW15pGPlan_word, fbW15pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW15pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 13 3 _ (canonT 64 (tensorPlanS 64 fbW15pGPlan t10X64))
      ((tensorWordDenAll fbW15pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW15pGX_chk.1 fbW15pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW15pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW15pH, ShortData.ofList fbW15pHT, 1 / 128,
    tensorRat 64 fbW15pHX ((tensorWordDenAll fbW15pH : ℚ) * 32 / 2 ^ 8)⟩

/-- The coordinates of the H image. -/
theorem fbW15pL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW15pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW15pL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW15pHW fbW15pH_check fbW15pHD
    fbW15pD_ok.1 fbW15pHD_cols fbW15pHD_rows fbW15pHT fbW15pHT_check _
    fbW15pH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW15pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW15pG, ShortData.ofList fbW15pGT, 1 / 32,
    tensorRat 64 fbW15pGX ((tensorWordDenAll fbW15pG : ℚ) * 32 / 2 ^ 13)⟩

/-- The coordinates of the G image. -/
theorem fbW15pW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW15pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW15pW.real :=
  IdentVec.word_actual t10V fbW15pGW fbW15pG_check fbW15pGD
    fbW15pD_ok.2 fbW15pGD_cols fbW15pGD_rows fbW15pGT fbW15pGT_check _
    fbW15pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
