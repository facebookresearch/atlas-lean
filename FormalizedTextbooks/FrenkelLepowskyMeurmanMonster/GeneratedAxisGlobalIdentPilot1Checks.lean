/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPilot1Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLettersInv
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindCosetBinary

/-! # Pilot identification data checks: Fifth root 1, positive triality

With `h₁ = xi⁻¹ P₀ P₁⁻¹ P₀⁻¹ P₁⁻¹` (the one-xi representative of Fifth root 1, worker `gfifth`)
and `g = q(4073160) σ(1024) h₁`, the triality image `sExtra (h₁ v₅)` of the Fifth axis is `g v₅`.
Both sides are local images of the Fifth axis: their representations are computed from
`fifthSrcVecW 64` (matrix by the spatial alphabet, short block by a checked transport onto the
literal target lists of `GeneratedAxisGlobalIdentShortPilot1Data`, tensor block by packed words),
and the pairing is evaluated in `GeneratedAxisGlobalIdentPilot1`.  This module certifies the
literal short data and binds both representations to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word `h₁`. -/
def pilot1H : List IdentLetter := pilot1Wh.map Prod.fst

/-- The destination word `g = q(4073160) σ(1024) h₁`. -/
def pilot1G : List IdentLetter := pilot1Wg.map Prod.fst

/-- The packed tensor of `h₁ v₅` (numerators over `256`). -/
def pilot1LX : List SVec := tensorWordAll 64 pilot1H (fifthSrcXW 64)

/-- The packed tensor of `g v₅` (numerators over `512`). -/
def pilot1WX : List SVec := tensorWordAll 64 pilot1G (fifthSrcXW 64)

/-- The representation of `h₁ v₅`. -/
def pilot1L : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet pilot1H, ShortData.ofList pilot1Th, 1 / 16,
    tensorRat 64 pilot1LX ((tensorWordDenAll pilot1H : ℚ) * 1)⟩

/-- The representation of `g v₅`. -/
def pilot1W : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet pilot1G, ShortData.ofList pilot1Tg, 1 / 16,
    tensorRat 64 pilot1WX ((tensorWordDenAll pilot1G : ℚ) * 1)⟩

/-! ## Checks of the literal short data -/

set_option maxRecDepth 100000 in
/-- The letter data of `h₁` are certified. -/
theorem pilot1Wh_check : pilot1Wh.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of `g` are certified. -/
theorem pilot1Wg_check : pilot1Wg.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem pilot1D_ok : pilot1Dh.ok = true ∧ pilot1Dg.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `h₁` evaluate the word on the generators. -/
theorem pilot1Dh_cols : ∀ i : Fin 24, qmWordP (pilot1Wh.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 pilot1Dh.colsP i.val, pilot1Dh.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `g` evaluate the word on the generators. -/
theorem pilot1Dg_cols : ∀ i : Fin 24, qmWordP (pilot1Wg.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 pilot1Dg.colsP i.val, pilot1Dg.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `h₁`. -/
theorem pilot1Dh_rows : ∀ i : Fin 24,
    fld 24 pilot1Dh.rowsP i.val = rowsOf (fun j => fld 24 pilot1Dh.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `g`. -/
theorem pilot1Dg_rows : ∀ i : Fin 24,
    fld 24 pilot1Dg.rowsP i.val = rowsOf (fun j => fld 24 pilot1Dg.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `h₁ v₅` is transported onto the literal targets. -/
theorem pilot1Th_check : shortCheckF pilot1Dh fifthSrcShort.flat pilot1Th = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `g v₅` is transported onto the literal targets. -/
theorem pilot1Tg_check : shortCheckF pilot1Dg fifthSrcShort.flat pilot1Tg = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem pilot1T_labels : pilot1Th.all (fun p => decide (p.1 < 98280)) = true ∧
    pilot1Tg.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-! ## The two local images -/

/-- The word bounds of `h₁`. -/
theorem pilot1H_growth : tensorWordGrowthAll pilot1H * 64 = 4194304 := by decide

/-- The word bounds of `g`. -/
theorem pilot1G_growth : tensorWordGrowthAll pilot1G * 64 = 33554432 := by decide

/-- The coordinates of `h₁ v₅`. -/
theorem pilot1L_actual : griessConwayEncode (rhoLocal (identWordLocal pilot1H)
    (generatedAxisGlobalTwelveRepresentative 4)) = pilot1L.real :=
  IdentVec.word_actual (fifthSrcVecW 64) pilot1Wh pilot1Wh_check pilot1Dh pilot1D_ok.1
    pilot1Dh_cols pilot1Dh_rows pilot1Th pilot1Th_check _
    (tensorWordAll_actual pilot1H (fifthSrcXW_bnd (by norm_num))
      (by rw [pilot1H_growth]; norm_num) 1).2 _ (fifthSrcW_rep (by norm_num))

/-- The coordinates of `g v₅`. -/
theorem pilot1W_actual : griessConwayEncode (rhoLocal (identWordLocal pilot1G)
    (generatedAxisGlobalTwelveRepresentative 4)) = pilot1W.real :=
  IdentVec.word_actual (fifthSrcVecW 64) pilot1Wg pilot1Wg_check pilot1Dg pilot1D_ok.2
    pilot1Dg_cols pilot1Dg_rows pilot1Tg pilot1Tg_check _
    (tensorWordAll_actual pilot1G (fifthSrcXW_bnd (by norm_num))
      (by rw [pilot1G_growth]; norm_num) 1).2 _ (fifthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
