/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW18pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW18pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W18+ (Twelfth root 18 to Tenth root 36, e = 1)

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
def fbW18pH : List IdentLetter := fbW18pHW.map Prod.fst

/-- The target word. -/
def fbW18pG : List IdentLetter := fbW18pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW18pHPlan_word : planWord fbW18pHPlan = fbW18pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW18pHPlan_ok : planOk fbW18pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW18pH_growth : tensorWordGrowthAll fbW18pH * 15 = 64424509440 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW18pH_den : tensorWordDenAll fbW18pH = 65536 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW18pH_check : fbW18pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW18pHD_cols : ∀ i : Fin 24, qmWordP (fbW18pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW18pHD.colsP i.val, fbW18pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW18pHD_rows : ∀ i : Fin 24,
    fld 24 fbW18pHD.rowsP i.val = rowsOf (fun j => fld 24 fbW18pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW18pGPlan_word : planWord fbW18pGPlan = fbW18pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW18pGPlan_ok : planOk fbW18pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW18pG_growth : tensorWordGrowthAll fbW18pG * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW18pG_den : tensorWordDenAll fbW18pG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW18pG_check : fbW18pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW18pGD_cols : ∀ i : Fin 24, qmWordP (fbW18pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW18pGD.colsP i.val, fbW18pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW18pGD_rows : ∀ i : Fin 24,
    fld 24 fbW18pGD.rowsP i.val = rowsOf (fun j => fld 24 fbW18pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW18pD_ok : fbW18pHD.ok = true ∧ fbW18pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW18pHT_labels : fbW18pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW18pGT_labels : fbW18pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^16`). -/
def fbW18pHX : List SVec := shiftT 16 (canonT 64 (tensorPlanS 64 fbW18pHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW18pHX_chk : colsLtB 64 4 fbW18pHX = true ∧
    fbW18pHX.map (sscale (2 ^ 16)) = canonT 64 (tensorPlanS 64 fbW18pHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW18pH_tensor : TBnd 64 (2 ^ 4 - 1) fbW18pHX ∧
    localTensorRepresentation (identWordFiber fbW18pH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW18pHX ((tensorWordDenAll fbW18pH : ℚ) * 32 / 2 ^ 16)) := by
  have hP := tensorPlanS_actual fbW18pHPlan fbW18pHPlan_ok fbt12X64_bnd
    (by rw [fbW18pHPlan_word, fbW18pH_growth]; norm_num) 32
  rw [fbW18pHPlan_word, fbW18pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW18pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 16 4 _ (canonT 64 (tensorPlanS 64 fbW18pHPlan fbt12X64))
      ((tensorWordDenAll fbW18pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW18pHX_chk.1 fbW18pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^9`). -/
def fbW18pGX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbW18pGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW18pGX_chk : colsLtB 64 4 fbW18pGX = true ∧
    fbW18pGX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbW18pGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW18pG_tensor : TBnd 64 (2 ^ 4 - 1) fbW18pGX ∧
    localTensorRepresentation (identWordFiber fbW18pG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW18pGX ((tensorWordDenAll fbW18pG : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbW18pGPlan fbW18pGPlan_ok t10X64_bnd
    (by rw [fbW18pGPlan_word, fbW18pG_growth]; norm_num) 32
  rw [fbW18pGPlan_word, fbW18pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW18pG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbW18pGPlan t10X64))
      ((tensorWordDenAll fbW18pG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW18pGX_chk.1 fbW18pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW18pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW18pH, ShortData.ofList fbW18pHT, 1 / 128,
    tensorRat 64 fbW18pHX ((tensorWordDenAll fbW18pH : ℚ) * 32 / 2 ^ 16)⟩

/-- The coordinates of the H image. -/
theorem fbW18pL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW18pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW18pL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW18pHW fbW18pH_check fbW18pHD
    fbW18pD_ok.1 fbW18pHD_cols fbW18pHD_rows fbW18pHT fbW18pHT_check _
    fbW18pH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW18pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW18pG, ShortData.ofList fbW18pGT, 1 / 32,
    tensorRat 64 fbW18pGX ((tensorWordDenAll fbW18pG : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the G image. -/
theorem fbW18pW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW18pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW18pW.real :=
  IdentVec.word_actual t10V fbW18pGW fbW18pG_check fbW18pGD
    fbW18pD_ok.2 fbW18pGD_cols fbW18pGD_rows fbW18pGT fbW18pGT_check _
    fbW18pG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
