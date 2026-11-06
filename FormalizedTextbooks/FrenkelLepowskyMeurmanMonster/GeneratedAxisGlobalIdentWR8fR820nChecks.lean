/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nChecksL

/-! # Factory checks (target side) of the identification Root8[25]- <-> Root8[25]- (record
r8f:R820-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wR8fR820nG_check : wR8fR820nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wR8fR820nGD_cols : ∀ i : Fin 24, qmWordP (wR8fR820nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR820nGD.colsP i.val, wR8fR820nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wR8fR820nGD_rows : ∀ i : Fin 24,
    fld 24 wR8fR820nGD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR820nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wR8fR820nGT_check : shortCheckF wR8fR820nGD srcRootEightCShort.flat wR8fR820nGT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wR8fR820nW_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR820nG)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR820nW.real := by
  have hT := (tensorWordAll_actual wR8fR820nG (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wR8fR820nG_growth]; norm_num) 32).2
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR820nGW wR8fR820nG_check wR8fR820nGD
      wR8fR820nD_ok.2 wR8fR820nGD_cols
    wR8fR820nGD_rows wR8fR820nGT wR8fR820nGT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
