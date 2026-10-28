/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W17+ (Twelfth root 17 to Tenth root 44, e = 1)

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
def fbW17pH : List IdentLetter := fbW17pHW.map Prod.fst

/-- The target word. -/
def fbW17pG : List IdentLetter := fbW17pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW17pHPlan_word : planWord fbW17pHPlan = fbW17pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW17pHPlan_ok : planOk fbW17pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW17pH_growth : tensorWordGrowthAll fbW17pH * 15 = 983040 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW17pH_den : tensorWordDenAll fbW17pH = 256 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW17pH_check : fbW17pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW17pHD_cols : ∀ i : Fin 24, qmWordP (fbW17pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW17pHD.colsP i.val, fbW17pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW17pHD_rows : ∀ i : Fin 24,
    fld 24 fbW17pHD.rowsP i.val = rowsOf (fun j => fld 24 fbW17pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW17pGPlan_word : planWord fbW17pGPlan = fbW17pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW17pGPlan_ok : planOk fbW17pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW17pG_growth : tensorWordGrowthAll fbW17pG * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW17pG_den : tensorWordDenAll fbW17pG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW17pG_check : fbW17pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW17pGD_cols : ∀ i : Fin 24, qmWordP (fbW17pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW17pGD.colsP i.val, fbW17pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW17pGD_rows : ∀ i : Fin 24,
    fld 24 fbW17pGD.rowsP i.val = rowsOf (fun j => fld 24 fbW17pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW17pD_ok : fbW17pHD.ok = true ∧ fbW17pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW17pHT_labels : fbW17pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW17pGT_labels : fbW17pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^8`). -/
def fbW17pHX : List SVec := shiftT 8 (canonT 64 (tensorPlanS 64 fbW17pHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW17pHX_chk : colsLtB 64 4 fbW17pHX = true ∧
    fbW17pHX.map (sscale (2 ^ 8)) = canonT 64 (tensorPlanS 64 fbW17pHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW17pH_tensor : TBnd 64 (2 ^ 4 - 1) fbW17pHX ∧
    localTensorRepresentation (identWordFiber fbW17pH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW17pHX ((tensorWordDenAll fbW17pH : ℚ) * 32 / 2 ^ 8)) := by
  have hP := tensorPlanS_actual fbW17pHPlan fbW17pHPlan_ok fbt12X64_bnd
    (by rw [fbW17pHPlan_word, fbW17pH_growth]; norm_num) 32
  rw [fbW17pHPlan_word, fbW17pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW17pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 8 4 _ (canonT 64 (tensorPlanS 64 fbW17pHPlan fbt12X64))
      ((tensorWordDenAll fbW17pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW17pHX_chk.1 fbW17pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^9`). -/
def fbW17pGX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbW17pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW17pGX_chk : colsLtB 64 4 fbW17pGX = true ∧
    fbW17pGX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbW17pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW17pG_tensor : TBnd 64 (2 ^ 4 - 1) fbW17pGX ∧
    localTensorRepresentation (identWordFiber fbW17pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW17pGX ((tensorWordDenAll fbW17pG : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbW17pGPlan fbW17pGPlan_ok t10X64_bnd
    (by rw [fbW17pGPlan_word, fbW17pG_growth]; norm_num) 32
  rw [fbW17pGPlan_word, fbW17pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW17pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbW17pGPlan t10X64))
      ((tensorWordDenAll fbW17pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW17pGX_chk.1 fbW17pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW17pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW17pH, ShortData.ofList fbW17pHT, 1 / 128,
    tensorRat 64 fbW17pHX ((tensorWordDenAll fbW17pH : ℚ) * 32 / 2 ^ 8)⟩

/-- The coordinates of the H image. -/
theorem fbW17pL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW17pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW17pL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW17pHW fbW17pH_check fbW17pHD
    fbW17pD_ok.1 fbW17pHD_cols fbW17pHD_rows fbW17pHT fbW17pHT_check _
    fbW17pH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW17pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW17pG, ShortData.ofList fbW17pGT, 1 / 32,
    tensorRat 64 fbW17pGX ((tensorWordDenAll fbW17pG : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the G image. -/
theorem fbW17pW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW17pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW17pW.real :=
  IdentVec.word_actual t10V fbW17pGW fbW17pG_check fbW17pGD
    fbW17pD_ok.2 fbW17pGD_cols fbW17pGD_rows fbW17pGT fbW17pGT_check _
    fbW17pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
