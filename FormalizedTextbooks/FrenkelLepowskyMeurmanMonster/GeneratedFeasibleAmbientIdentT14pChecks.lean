/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX

/-! # Checks of the identification gtenth:T14+ (Tenth root 14 to Twelfth root 7, e = 1)

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
def fbT14pH : List IdentLetter := fbT14pHW.map Prod.fst

/-- The target word. -/
def fbT14pG : List IdentLetter := fbT14pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbT14pHPlan_word : planWord fbT14pHPlan = fbT14pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbT14pHPlan_ok : planOk fbT14pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbT14pH_growth : tensorWordGrowthAll fbT14pH * 15 = 64424509440 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbT14pH_den : tensorWordDenAll fbT14pH = 65536 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbT14pH_check : fbT14pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbT14pHD_cols : ∀ i : Fin 24, qmWordP (fbT14pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbT14pHD.colsP i.val, fbT14pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbT14pHD_rows : ∀ i : Fin 24,
    fld 24 fbT14pHD.rowsP i.val = rowsOf (fun j => fld 24 fbT14pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbT14pGPlan_word : planWord fbT14pGPlan = fbT14pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbT14pGPlan_ok : planOk fbT14pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbT14pG_growth : tensorWordGrowthAll fbT14pG * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbT14pG_den : tensorWordDenAll fbT14pG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbT14pG_check : fbT14pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbT14pGD_cols : ∀ i : Fin 24, qmWordP (fbT14pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbT14pGD.colsP i.val, fbT14pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbT14pGD_rows : ∀ i : Fin 24,
    fld 24 fbT14pGD.rowsP i.val = rowsOf (fun j => fld 24 fbT14pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbT14pD_ok : fbT14pHD.ok = true ∧ fbT14pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbT14pHT_labels : fbT14pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbT14pGT_labels : fbT14pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^16`). -/
def fbT14pHX : List SVec := shiftT 16 (canonT 64 (tensorPlanS 64 fbT14pHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^3` and is exact. -/
theorem fbT14pHX_chk : colsLtB 64 3 fbT14pHX = true ∧
    fbT14pHX.map (sscale (2 ^ 16)) = canonT 64 (tensorPlanS 64 fbT14pHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbT14pH_tensor : TBnd 64 (2 ^ 3 - 1) fbT14pHX ∧
    localTensorRepresentation (identWordFiber fbT14pH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbT14pHX ((tensorWordDenAll fbT14pH : ℚ) * 32 / 2 ^ 16)) := by
  have hP := tensorPlanS_actual fbT14pHPlan fbT14pHPlan_ok t10X64_bnd
    (by rw [fbT14pHPlan_word, fbT14pH_growth]; norm_num) 32
  rw [fbT14pHPlan_word, fbT14pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbT14pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 16 3 _ (canonT 64 (tensorPlanS 64 fbT14pHPlan t10X64))
      ((tensorWordDenAll fbT14pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbT14pHX_chk.1 fbT14pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^9`). -/
def fbT14pGX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbT14pGPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbT14pGX_chk : colsLtB 64 4 fbT14pGX = true ∧
    fbT14pGX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbT14pGPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbT14pG_tensor : TBnd 64 (2 ^ 4 - 1) fbT14pGX ∧
    localTensorRepresentation (identWordFiber fbT14pG)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbT14pGX ((tensorWordDenAll fbT14pG : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbT14pGPlan fbT14pGPlan_ok fbt12X64_bnd
    (by rw [fbT14pGPlan_word, fbT14pG_growth]; norm_num) 32
  rw [fbT14pGPlan_word, fbT14pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbT14pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbT14pGPlan fbt12X64))
      ((tensorWordDenAll fbT14pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbT14pGX_chk.1 fbT14pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbT14pL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbT14pH, ShortData.ofList fbT14pHT, 1 / 32,
    tensorRat 64 fbT14pHX ((tensorWordDenAll fbT14pH : ℚ) * 32 / 2 ^ 16)⟩

/-- The coordinates of the H image. -/
theorem fbT14pL_actual : griessConwayEncode (rhoLocal (identWordLocal fbT14pH)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbT14pL.real :=
  IdentVec.word_actual t10V fbT14pHW fbT14pH_check fbT14pHD
    fbT14pD_ok.1 fbT14pHD_cols fbT14pHD_rows fbT14pHT fbT14pHT_check _
    fbT14pH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def fbT14pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbT14pG, ShortData.ofList fbT14pGT, 1 / 128,
    tensorRat 64 fbT14pGX ((tensorWordDenAll fbT14pG : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the G image. -/
theorem fbT14pW_actual : griessConwayEncode (rhoLocal (identWordLocal fbT14pG)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbT14pW.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbT14pGW fbT14pG_check fbT14pGD
    fbT14pD_ok.2 fbT14pGD_cols fbT14pGD_rows fbT14pGT fbT14pGT_check _
    fbT14pG_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
