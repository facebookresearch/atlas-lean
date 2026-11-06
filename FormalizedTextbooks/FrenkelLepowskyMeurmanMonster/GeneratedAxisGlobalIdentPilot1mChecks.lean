/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1Vec

/-! # Pilot identification data checks: Fifth root 1, inverse triality

The destination `g' v₅` with `g' = q(6293364) σ(32) h₁`: its representation (matrix by the
spatial alphabet, short block by the checked transport onto `pilot1mTg`, tensor block by packed
words), bound to the genuine coordinates; the side conditions of the pairing with `h₁ v₅`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The destination word `g' = q(6293364) σ(32) h₁`. -/
def pilot1mG : List IdentLetter := pilot1mWg.map Prod.fst

/-- The packed tensor of `g' v₅` (numerators over `512`). -/
def pilot1mWX : List SVec := tensorWordAll 64 pilot1mG (fifthSrcXW 64)

/-- The representation of `g' v₅`. -/
def pilot1mW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet pilot1mG, ShortData.ofList pilot1mTg, 1 / 16,
    tensorRat 64 pilot1mWX ((tensorWordDenAll pilot1mG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of `g'` are certified. -/
theorem pilot1mWg_check : pilot1mWg.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem pilot1mDg_ok : pilot1mDg.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `g'` evaluate the word on the generators. -/
theorem pilot1mDg_cols : ∀ i : Fin 24, qmWordP (pilot1mWg.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 pilot1mDg.colsP i.val, pilot1mDg.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `g'`. -/
theorem pilot1mDg_rows : ∀ i : Fin 24,
    fld 24 pilot1mDg.rowsP i.val = rowsOf (fun j => fld 24 pilot1mDg.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `g' v₅` is transported onto the literal targets. -/
theorem pilot1mTg_check : shortCheckF pilot1mDg fifthSrcShort.flat pilot1mTg = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem pilot1mTg_labels : pilot1mTg.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The word bound of `g'`. -/
theorem pilot1mG_growth : tensorWordGrowthAll pilot1mG * 64 = 33554432 := by decide

/-- The coordinates of `g' v₅`. -/
theorem pilot1mW_actual : griessConwayEncode (rhoLocal (identWordLocal pilot1mG)
    (generatedAxisGlobalTwelveRepresentative 4)) = pilot1mW.real :=
  IdentVec.word_actual (fifthSrcVecW 64) pilot1mWg pilot1mWg_check pilot1mDg pilot1mDg_ok
    pilot1mDg_cols pilot1mDg_rows pilot1mTg pilot1mTg_check _
    (tensorWordAll_actual pilot1mG (fifthSrcXW_bnd (by norm_num))
      (by rw [pilot1mG_growth]; norm_num) 1).2 _ (fifthSrcW_rep (by norm_num))

/-- The short block of `g' v₅` satisfies the range conditions. -/
theorem pilot1mW_ok : pilot1mW.sh.ok = true := ofList_ok pilot1mTg pilot1mTg_labels

set_option maxRecDepth 100000 in
/-- The coefficient sum of the odd terms of `g' v₅`. -/
theorem pilot1m_absSum : absSumO pilot1mW.sh.odd = 4096 := by decide +kernel

/-- The numeric side conditions of the inverse pilot pairing. -/
theorem pilot1m_bounds : PairXBounds 64 4194304 33554432 pilot1Lg pilot1mW := by
  obtain ⟨h1, -⟩ := pilot1_absSum
  have h2 := pilot1m_absSum
  exact ⟨by norm_num, by norm_num, by norm_num, by rw [h2]; norm_num, by rw [h2]; norm_num,
    by rw [h1]; norm_num, by rw [h1]; norm_num⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
