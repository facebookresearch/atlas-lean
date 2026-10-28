/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentYData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource

/-! # The incoming Twelfth vector as an identification vector

The Twelfth axis is `sExtra y` for the local image `y = rhoLocal generatedTwelfthLocal v₅` of the
Fifth axis. `twelfthYVec` represents `y` exactly (`twelfthY_actual`): the word image of
`fifthSrcVec` under the Twelfth source word, with the letter data, the composite mask data and
the short image list certified by the kernel, the matrix block by the spatial alphabet and the
tensor block by the packed word action `tensorWordAll`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The packed tensor of the incoming Twelfth vector. -/
def twelfthYX : List SVec := tensorWordAll 128 twelfthYWord fifthSrcX

/-- The incoming Twelfth vector `rhoLocal generatedTwelfthLocal v₅` as an identification vector. -/
def twelfthYVec : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet twelfthYWord, ShortData.ofList twelfthYT, 1 / 16,
    tensorRat 128 twelfthYX ((tensorWordDenAll twelfthYWord : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the Twelfth source word are certified. -/
theorem twelfthY_letters :
    (twelfthWordData twelfthYWord).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite mask data of the Twelfth source word are certified. -/
theorem twelfthY_composite : twelfthYD.ok = true ∧
    (∀ i : Fin 24, qmWordP ((twelfthWordData twelfthYWord).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 twelfthYD.colsP i.val, twelfthYD.coeff.testBit i.val)) ∧
    (∀ i : Fin 24,
      fld 24 twelfthYD.rowsP i.val = rowsOf (fun j => fld 24 twelfthYD.colsP j.val) i) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list is the checked transport of the Fifth short block. -/
theorem twelfthY_short : shortCheckF twelfthYD fifthSrcVec.sh.flat twelfthYT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list has valid labels. -/
theorem twelfthY_labels : twelfthYT.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- Field bound for the packed word action. -/
theorem twelfthY_growth : tensorWordGrowthAll twelfthYWord * 64 < 2 ^ 128 := by
  decide +kernel

/-- The tensor block of the incoming representation. -/
theorem twelfthYVec_ten :
    twelfthYVec.ten = tensorRat 128 twelfthYX ((tensorWordDenAll twelfthYWord : ℚ) * 1) := rfl

/-- Bounds of the packed incoming tensor. -/
theorem twelfthYX_bnd : TBnd 128 (tensorWordGrowthAll twelfthYWord * 64) twelfthYX :=
  (tensorWordAll_actual twelfthYWord fifthSrcX_bnd twelfthY_growth 1).1

/-- The short block of the incoming representation satisfies the range conditions. -/
theorem twelfthYVec_ok : twelfthYVec.sh.ok = true := ofList_ok _ twelfthY_labels

/-- The incoming Twelfth vector is represented exactly. -/
theorem twelfthY_actual :
    griessConwayEncode (rhoLocal generatedTwelfthLocal generatedFifthAxis) = twelfthYVec.real := by
  have hT := (tensorWordAll_actual twelfthYWord fifthSrcX_bnd twelfthY_growth 1).2
  have hT' : localTensorRepresentation
      (identWordFiber ((twelfthWordData twelfthYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal fifthSrcVec.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 128 twelfthYX ((tensorWordDenAll twelfthYWord : ℚ) * 1)) := by
    rw [twelfthWordData_fst, fifthSrcVec_ten]
    exact hT
  have h := IdentVec.word_actual fifthSrcVec (twelfthWordData twelfthYWord) twelfthY_letters
    twelfthYD twelfthY_composite.1 twelfthY_composite.2.1 twelfthY_composite.2.2 twelfthYT
    twelfthY_short _ hT' _ fifthSrc_actual
  rw [twelfthWordData_fst] at h
  rw [← twelfthYWord_local]
  exact h

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
