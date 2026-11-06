/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the identification gtwelfth:W15- (Twelfth root 15 to Tenth root 38, e = -1)

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
def fbW15nH : List IdentLetter := fbW15nHW.map Prod.fst

/-- The target word. -/
def fbW15nG : List IdentLetter := fbW15nGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem fbW15nHPlan_word : planWord fbW15nHPlan = fbW15nH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem fbW15nHPlan_ok : planOk fbW15nHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem fbW15nH_growth : tensorWordGrowthAll fbW15nH * 15 = 983040 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem fbW15nH_den : tensorWordDenAll fbW15nH = 256 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem fbW15nH_check : fbW15nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem fbW15nHD_cols : ∀ i : Fin 24, qmWordP (fbW15nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW15nHD.colsP i.val, fbW15nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem fbW15nHD_rows : ∀ i : Fin 24,
    fld 24 fbW15nHD.rowsP i.val = rowsOf (fun j => fld 24 fbW15nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem fbW15nGPlan_word : planWord fbW15nGPlan = fbW15nG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem fbW15nGPlan_ok : planOk fbW15nGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem fbW15nG_growth : tensorWordGrowthAll fbW15nG * 15 = 2013265920 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem fbW15nG_den : tensorWordDenAll fbW15nG = 8192 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem fbW15nG_check : fbW15nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem fbW15nGD_cols : ∀ i : Fin 24, qmWordP (fbW15nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 fbW15nGD.colsP i.val, fbW15nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem fbW15nGD_rows : ∀ i : Fin 24,
    fld 24 fbW15nGD.rowsP i.val = rowsOf (fun j => fld 24 fbW15nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fbW15nD_ok : fbW15nHD.ok = true ∧ fbW15nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW15nHT_labels : fbW15nHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem fbW15nGT_labels : fbW15nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^8`). -/
def fbW15nHX : List SVec := shiftT 8 (canonT 64 (tensorPlanS 64 fbW15nHPlan fbt12X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^3` and is exact. -/
theorem fbW15nHX_chk : colsLtB 64 3 fbW15nHX = true ∧
    fbW15nHX.map (sscale (2 ^ 8)) = canonT 64 (tensorPlanS 64 fbW15nHPlan fbt12X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem fbW15nH_tensor : TBnd 64 (2 ^ 3 - 1) fbW15nHX ∧
    localTensorRepresentation (identWordFiber fbW15nH)
        (generatedAxisGlobalRationalTensorReal (twelfthSrcVecS 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW15nHX ((tensorWordDenAll fbW15nH : ℚ) * 32 / 2 ^ 8)) := by
  have hP := tensorPlanS_actual fbW15nHPlan fbW15nHPlan_ok fbt12X64_bnd
    (by rw [fbW15nHPlan_word, fbW15nH_growth]; norm_num) 32
  rw [fbW15nHPlan_word, fbW15nH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW15nH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 8 3 _ (canonT 64 (tensorPlanS 64 fbW15nHPlan fbt12X64))
      ((tensorWordDenAll fbW15nH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW15nHX_chk.1 fbW15nHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fbt12V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^13`). -/
def fbW15nGX : List SVec := shiftT 13 (canonT 64 (tensorPlanS 64 fbW15nGPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^3` and is exact. -/
theorem fbW15nGX_chk : colsLtB 64 3 fbW15nGX = true ∧
    fbW15nGX.map (sscale (2 ^ 13)) = canonT 64 (tensorPlanS 64 fbW15nGPlan t10X64) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem fbW15nG_tensor : TBnd 64 (2 ^ 3 - 1) fbW15nGX ∧
    localTensorRepresentation (identWordFiber fbW15nG)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 fbW15nGX ((tensorWordDenAll fbW15nG : ℚ) * 32 / 2 ^ 13)) := by
  have hP := tensorPlanS_actual fbW15nGPlan fbW15nGPlan_ok t10X64_bnd
    (by rw [fbW15nGPlan_word, fbW15nG_growth]; norm_num) 32
  rw [fbW15nGPlan_word, fbW15nG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll fbW15nG : ℚ) * 32)
  have hs := tensorRat_shiftT 64 13 3 _ (canonT 64 (tensorPlanS 64 fbW15nGPlan t10X64))
      ((tensorWordDenAll fbW15nG : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) fbW15nGX_chk.1 fbW15nGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def fbW15nL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet fbW15nH, ShortData.ofList fbW15nHT, 1 / 128,
    tensorRat 64 fbW15nHX ((tensorWordDenAll fbW15nH : ℚ) * 32 / 2 ^ 8)⟩

/-- The coordinates of the H image. -/
theorem fbW15nL_actual : griessConwayEncode (rhoLocal (identWordLocal fbW15nH)
    (generatedAxisGlobalTwelveRepresentative 10)) = fbW15nL.real :=
  IdentVec.word_actual (twelfthSrcVecS 64) fbW15nHW fbW15nH_check fbW15nHD
    fbW15nD_ok.1 fbW15nHD_cols fbW15nHD_rows fbW15nHT fbW15nHT_check _
    fbW15nH_tensor.2 _ (twelfthSrcS_rep (w := 64) (by norm_num))

/-- The representation of the G image. -/
def fbW15nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet fbW15nG, ShortData.ofList fbW15nGT, 1 / 32,
    tensorRat 64 fbW15nGX ((tensorWordDenAll fbW15nG : ℚ) * 32 / 2 ^ 13)⟩

/-- The coordinates of the G image. -/
theorem fbW15nW_actual : griessConwayEncode (rhoLocal (identWordLocal fbW15nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = fbW15nW.real :=
  IdentVec.word_actual t10V fbW15nGW fbW15nG_check fbW15nGD
    fbW15nD_ok.2 fbW15nGD_cols fbW15nGD_rows fbW15nGT fbW15nGT_check _
    fbW15nG_tensor.2 _ t10V_rep

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
