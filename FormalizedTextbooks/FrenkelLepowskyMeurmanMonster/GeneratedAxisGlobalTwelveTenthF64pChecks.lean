/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pSH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pSG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthScale
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcX

/-! # Checks of the Tenth identification T64+ (gtenth)

Letter, composite and label checks; the tensor blocks of both images by fast plans, canonical form
    and
exact division; the representations of both images bound to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def tf64pH : List IdentLetter := tf64pHW.map Prod.fst

/-- The target word. -/
def tf64pG : List IdentLetter := tf64pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The plan expands to the H word. -/
theorem tf64pHPlan_word : planWord tf64pHPlan = tf64pH := rfl

set_option maxRecDepth 100000 in
/-- The runs of the H plan are admissible. -/
theorem tf64pHPlan_ok : planOk tf64pHPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the H word. -/
theorem tf64pH_growth : tensorWordGrowthAll tf64pH * 15 = 2013265920 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the H word. -/
theorem tf64pH_den : tensorWordDenAll tf64pH = 8192 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the H word are certified. -/
theorem tf64pH_check : tf64pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the H word evaluate the word on the generators. -/
theorem tf64pHD_cols : ∀ i : Fin 24, qmWordP (tf64pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tf64pHD.colsP i.val, tf64pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the H word. -/
theorem tf64pHD_rows : ∀ i : Fin 24,
    fld 24 tf64pHD.rowsP i.val = rowsOf (fun j => fld 24 tf64pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The plan expands to the G word. -/
theorem tf64pGPlan_word : planWord tf64pGPlan = tf64pG := rfl

set_option maxRecDepth 100000 in
/-- The runs of the G plan are admissible. -/
theorem tf64pGPlan_ok : planOk tf64pGPlan = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The growth bound of the G word. -/
theorem tf64pG_growth : tensorWordGrowthAll tf64pG * 56 = 7516192768 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The denominator factor of the G word. -/
theorem tf64pG_den : tensorWordDenAll tf64pG = 8192 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the G word are certified. -/
theorem tf64pG_check : tf64pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the G word evaluate the word on the generators. -/
theorem tf64pGD_cols : ∀ i : Fin 24, qmWordP (tf64pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 tf64pGD.colsP i.val, tf64pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the G word. -/
theorem tf64pGD_rows : ∀ i : Fin 24,
    fld 24 tf64pGD.rowsP i.val = rowsOf (fun j => fld 24 tf64pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem tf64pD_ok : tf64pHD.ok = true ∧ tf64pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tf64pHT_labels : tf64pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The transported lists have valid labels. -/
theorem tf64pGT_labels : tf64pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The tight packed tensor of the H image (canonical form divided by `2^13`). -/
noncomputable def tf64pHX : List SVec := shiftT 13 (canonT 64 (tensorPlanS 64 tf64pHPlan t10X64))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^4` and is exact. -/
theorem tf64pHX_chk : colsLtB 64 4 tf64pHX = true ∧
    tf64pHX.map (sscale (2 ^ 13)) = canonT 64 (tensorPlanS 64 tf64pHPlan t10X64) := by
  decide +kernel

/-- The tensor block of the H image: tight bound and the genuine tensor action. -/
theorem tf64pH_tensor : TBnd 64 (2 ^ 4 - 1) tf64pHX ∧
    localTensorRepresentation (identWordFiber tf64pH)
        (generatedAxisGlobalRationalTensorReal t10V.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tf64pHX ((tensorWordDenAll tf64pH : ℚ) * 32 / 2 ^ 13)) := by
  have hP := tensorPlanS_actual tf64pHPlan tf64pHPlan_ok t10X64_bnd
    (by rw [tf64pHPlan_word, tf64pH_growth]; norm_num) 32
  rw [tf64pHPlan_word, tf64pH_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tf64pH : ℚ) * 32)
  have hs := tensorRat_shiftT 64 13 4 _ (canonT 64 (tensorPlanS 64 tf64pHPlan t10X64))
      ((tensorWordDenAll tf64pH : ℚ) * 32)
    hc.1 (by norm_num) (by norm_num) tf64pHX_chk.1 tf64pHX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [t10V_ten64, hP.2, ← hc.2, hs.2]
  rfl

/-- The tight packed tensor of the G image (canonical form divided by `2^8`). -/
noncomputable def tf64pGX : List SVec := shiftT 8 (canonT 64 (tensorPlanS 64 tf64pGPlan
    (fourthSrcXW 64)))

set_option maxRecDepth 100000 in
/-- The tight tensor has fields below `2^3` and is exact. -/
theorem tf64pGX_chk : colsLtB 64 3 tf64pGX = true ∧
    tf64pGX.map (sscale (2 ^ 8)) = canonT 64 (tensorPlanS 64 tf64pGPlan (fourthSrcXW 64)) := by
  decide +kernel

/-- The tensor block of the G image: tight bound and the genuine tensor action. -/
theorem tf64pG_tensor : TBnd 64 (2 ^ 3 - 1) tf64pGX ∧
    localTensorRepresentation (identWordFiber tf64pG)
        (generatedAxisGlobalRationalTensorReal (fourthSrcVecW 64).ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 64 tf64pGX ((tensorWordDenAll tf64pG : ℚ) * 1 / 2 ^ 8)) := by
  have hP := tensorPlanS_actual tf64pGPlan tf64pGPlan_ok (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [tf64pGPlan_word, tf64pG_growth]; norm_num) 1
  rw [tf64pGPlan_word, tf64pG_growth] at hP
  have hc := canonT_spec (by norm_num) hP.1 (by norm_num) ((tensorWordDenAll tf64pG : ℚ) * 1)
  have hs := tensorRat_shiftT 64 8 3 _ (canonT 64 (tensorPlanS 64 tf64pGPlan (fourthSrcXW 64)))
      ((tensorWordDenAll tf64pG : ℚ) * 1)
    hc.1 (by norm_num) (by norm_num) tf64pGX_chk.1 tf64pGX_chk.2
  refine ⟨hs.1, ?_⟩
  rw [fourthSrcVecW_ten, hP.2, ← hc.2, hs.2]
  rfl

/-- The representation of the H image. -/
def tf64pL : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet tf64pH, ShortData.ofList tf64pHT, 1 / 32,
    tensorRat 64 tf64pHX ((tensorWordDenAll tf64pH : ℚ) * 32 / 2 ^ 13)⟩

/-- The coordinates of the H image. -/
theorem tf64pL_actual : griessConwayEncode (rhoLocal (identWordLocal tf64pH)
    (generatedAxisGlobalTwelveRepresentative 11)) = tf64pL.real :=
  IdentVec.word_actual t10V tf64pHW tf64pH_check tf64pHD
    tf64pD_ok.1 tf64pHD_cols tf64pHD_rows tf64pHT tf64pHT_check _
    tf64pH_tensor.2 _ t10V_rep

/-- The representation of the G image. -/
def tf64pW : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet tf64pG, ShortData.ofList tf64pGT, 1 / 8,
    tensorRat 64 tf64pGX ((tensorWordDenAll tf64pG : ℚ) * 1 / 2 ^ 8)⟩

/-- The coordinates of the G image. -/
theorem tf64pW_actual : griessConwayEncode (rhoLocal (identWordLocal tf64pG)
    (generatedAxisGlobalTwelveRepresentative 3)) = tf64pW.real :=
  IdentVec.word_actual (fourthSrcVecW 64) tf64pGW tf64pG_check tf64pGD
    tf64pD_ok.2 tf64pGD_cols tf64pGD_rows tf64pGT tf64pGT_check _
    tf64pG_tensor.2 _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
