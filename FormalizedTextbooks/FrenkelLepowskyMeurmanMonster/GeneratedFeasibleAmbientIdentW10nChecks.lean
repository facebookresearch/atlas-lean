/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W10- (Twelfth root 10 to Tenth root 51, e = -1)

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
def fbW10nH : List IdentLetter := fbW10nHW.map Prod.fst

/-- The target word. -/
def fbW10nG : List IdentLetter := fbW10nGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW10nHPlan_word : planWord fbW10nHPlan = fbW10nH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW10nHPlan_ok : planOk fbW10nHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW10nH_growth : tensorWordGrowthAll fbW10nH * 15 = 983040 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW10nH_den : tensorWordDenAll fbW10nH = 256 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW10nH_check : fbW10nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW10nHD_cols : ∀ i : Fin 24, qmWordP (fbW10nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW10nHD.colsP i.val, fbW10nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW10nHD_rows : ∀ i : Fin 24,
    fld 24 fbW10nHD.rowsP i.val = rowsOf (fun j => fld 24 fbW10nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW10nGPlan_word : planWord fbW10nGPlan = fbW10nG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW10nGPlan_ok : planOk fbW10nGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW10nG_growth : tensorWordGrowthAll fbW10nG * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW10nG_den : tensorWordDenAll fbW10nG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW10nG_check : fbW10nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW10nGD_cols : ∀ i : Fin 24, qmWordP (fbW10nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW10nGD.colsP i.val, fbW10nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW10nGD_rows : ∀ i : Fin 24,
    fld 24 fbW10nGD.rowsP i.val = rowsOf (fun j => fld 24 fbW10nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW10nD_ok : fbW10nHD.ok = true ∧ fbW10nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW10nHT_labels : fbW10nHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW10nGT_labels : fbW10nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^8`). -/
def fbW10nHX : List SVec := shiftT 8 (canonT 64 (tensorPlanS 64 fbW10nHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW10nHX_chk : colsLtB 64 4 fbW10nHX = true ∧
    fbW10nHX.map (sscale (2 ^ 8)) = canonT 64 (tensorPlanS 64 fbW10nHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW10nH_tensor : TBnd 64 (2 ^ 4 - 1) fbW10nHX ∧
    localTensorRepresentation (identWordFiber fbW10nH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW10nHX ((tensorWordDenAll fbW10nH : ℚ) * 32 / 2 ^ 8)) := by
  have hP := tensorPlanS_actual fbW10nHPlan fbW10nHPlan_ok fbt12X64_bnd
    (by rw [fbW10nHPlan_word, fbW10nH_growth]; norm_num) 32
  rw [fbW10nHPlan_word, fbW10nH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW10nH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 8 4 _ (canonT 64 (tensorPlanS 64 fbW10nHPlan fbt12X64))
      ((tensorWordDenAll fbW10nH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW10nHX_chk.1 fbW10nHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^9`). -/
def fbW10nGX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbW10nGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW10nGX_chk : colsLtB 64 4 fbW10nGX = true ∧
    fbW10nGX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbW10nGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW10nG_tensor : TBnd 64 (2 ^ 4 - 1) fbW10nGX ∧
    localTensorRepresentation (identWordFiber fbW10nG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW10nGX ((tensorWordDenAll fbW10nG : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbW10nGPlan fbW10nGPlan_ok t10X64_bnd
    (by rw [fbW10nGPlan_word, fbW10nG_growth]; norm_num) 32
  rw [fbW10nGPlan_word, fbW10nG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW10nG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbW10nGPlan t10X64))
      ((tensorWordDenAll fbW10nG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW10nGX_chk.1 fbW10nGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW10nL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW10nH, ShortData.ofList fbW10nHT, 1 / 128,
    tensorRat 64 fbW10nHX ((tensorWordDenAll fbW10nH : ℚ) * 32 / 2 ^ 8)⟩

/-- The coordinates of the H image. -/
theorem fbW10nL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW10nH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW10nL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW10nHW fbW10nH_check fbW10nHD
    fbW10nD_ok.1 fbW10nHD_cols fbW10nHD_rows fbW10nHT fbW10nHT_check _
    fbW10nH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW10nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW10nG, ShortData.ofList fbW10nGT, 1 / 32,
    tensorRat 64 fbW10nGX ((tensorWordDenAll fbW10nG : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the G image. -/
theorem fbW10nW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW10nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW10nW.real :=
  IdentVec.word_actual t10V fbW10nGW fbW10nG_check fbW10nGD
    fbW10nD_ok.2 fbW10nGD_cols fbW10nGD_rows fbW10nGT fbW10nGT_check _
    fbW10nG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
