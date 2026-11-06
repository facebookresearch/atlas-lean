/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W16- (Twelfth root 16 to Tenth root 28, e = -1)

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
def fbW16nH : List IdentLetter := fbW16nHW.map Prod.fst

/-- The target word. -/
def fbW16nG : List IdentLetter := fbW16nGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW16nHPlan_word : planWord fbW16nHPlan = fbW16nH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW16nHPlan_ok : planOk fbW16nHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW16nH_growth : tensorWordGrowthAll fbW16nH * 15 = 983040 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW16nH_den : tensorWordDenAll fbW16nH = 256 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW16nH_check : fbW16nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW16nHD_cols : ∀ i : Fin 24, qmWordP (fbW16nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW16nHD.colsP i.val, fbW16nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW16nHD_rows : ∀ i : Fin 24,
    fld 24 fbW16nHD.rowsP i.val = rowsOf (fun j => fld 24 fbW16nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW16nGPlan_word : planWord fbW16nGPlan = fbW16nG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW16nGPlan_ok : planOk fbW16nGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW16nG_growth : tensorWordGrowthAll fbW16nG * 15 = 7864320 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW16nG_den : tensorWordDenAll fbW16nG = 512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW16nG_check : fbW16nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW16nGD_cols : ∀ i : Fin 24, qmWordP (fbW16nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW16nGD.colsP i.val, fbW16nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW16nGD_rows : ∀ i : Fin 24,
    fld 24 fbW16nGD.rowsP i.val = rowsOf (fun j => fld 24 fbW16nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW16nD_ok : fbW16nHD.ok = true ∧ fbW16nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW16nHT_labels : fbW16nHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW16nGT_labels : fbW16nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^8`). -/
def fbW16nHX : List SVec := shiftT 8 (canonT 64 (tensorPlanS 64 fbW16nHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW16nHX_chk : colsLtB 64 4 fbW16nHX = true ∧
    fbW16nHX.map (sscale (2 ^ 8)) = canonT 64 (tensorPlanS 64 fbW16nHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW16nH_tensor : TBnd 64 (2 ^ 4 - 1) fbW16nHX ∧
    localTensorRepresentation (identWordFiber fbW16nH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW16nHX ((tensorWordDenAll fbW16nH : ℚ) * 32 / 2 ^ 8)) := by
  have hP := tensorPlanS_actual fbW16nHPlan fbW16nHPlan_ok fbt12X64_bnd
    (by rw [fbW16nHPlan_word, fbW16nH_growth]; norm_num) 32
  rw [fbW16nHPlan_word, fbW16nH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW16nH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 8 4 _ (canonT 64 (tensorPlanS 64 fbW16nHPlan fbt12X64))
      ((tensorWordDenAll fbW16nH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW16nHX_chk.1 fbW16nHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^9`). -/
def fbW16nGX : List SVec := shiftT 9 (canonT 64 (tensorPlanS 64 fbW16nGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem fbW16nGX_chk : colsLtB 64 4 fbW16nGX = true ∧
    fbW16nGX.map (sscale (2 ^ 9)) = canonT 64 (tensorPlanS 64 fbW16nGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW16nG_tensor : TBnd 64 (2 ^ 4 - 1) fbW16nGX ∧
    localTensorRepresentation (identWordFiber fbW16nG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW16nGX ((tensorWordDenAll fbW16nG : ℚ) * 32 / 2 ^ 9)) := by
  have hP := tensorPlanS_actual fbW16nGPlan fbW16nGPlan_ok t10X64_bnd
    (by rw [fbW16nGPlan_word, fbW16nG_growth]; norm_num) 32
  rw [fbW16nGPlan_word, fbW16nG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW16nG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 9 4 _ (canonT 64 (tensorPlanS 64 fbW16nGPlan t10X64))
      ((tensorWordDenAll fbW16nG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW16nGX_chk.1 fbW16nGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW16nL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW16nH, ShortData.ofList fbW16nHT, 1 / 128,
    tensorRat 64 fbW16nHX ((tensorWordDenAll fbW16nH : ℚ) * 32 / 2 ^ 8)⟩

/-- The coordinates of the H image. -/
theorem fbW16nL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW16nH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW16nL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW16nHW fbW16nH_check fbW16nHD
    fbW16nD_ok.1 fbW16nHD_cols fbW16nHD_rows fbW16nHT fbW16nHT_check _
    fbW16nH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW16nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW16nG, ShortData.ofList fbW16nGT, 1 / 32,
    tensorRat 64 fbW16nGX ((tensorWordDenAll fbW16nG : ℚ) * 32 / 2 ^ 9)⟩

/-- The coordinates of the G image. -/
theorem fbW16nW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW16nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW16nW.real :=
  IdentVec.word_actual t10V fbW16nGW fbW16nG_check fbW16nGD
    fbW16nD_ok.2 fbW16nGD_cols fbW16nGD_rows fbW16nGT fbW16nGT_check _
    fbW16nG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
