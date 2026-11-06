/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcNinthData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource

/-! # The incoming Ninth vector as an identification vector

The Ninth axis is `sExtra y` for the local image `y` of the Fifth axis under the
Ninth source word. `srcNinthYVec` represents `y` exactly (`srcNinthY_actual`): the
word image of `fifthSrcVec`, with the letter data, the composite mask data and the short image
list certified by the kernel, the matrix block by the spatial alphabet and the tensor block by
the packed word action `tensorWordAll`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The packed tensor of the incoming Ninth vector. -/
def srcNinthYX : List SVec := tensorWordAll 128 srcNinthYWord fifthSrcX

/-- The incoming Ninth vector as an identification vector. -/
noncomputable def srcNinthYVec : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet srcNinthYWord, ShortData.ofList srcNinthYT, 1 / 16,
    tensorRat 128 srcNinthYX ((tensorWordDenAll srcNinthYWord : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the Ninth source word are certified. -/
theorem srcNinthY_letters :
    (srcWordData srcNinthYWord).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite mask data of the Ninth source word are certified. -/
theorem srcNinthY_composite : srcNinthYD.ok = true ∧
    (∀ i : Fin 24, qmWordP ((srcWordData srcNinthYWord).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 srcNinthYD.colsP i.val, srcNinthYD.coeff.testBit i.val)) ∧
    (∀ i : Fin 24,
      fld 24 srcNinthYD.rowsP i.val =
        rowsOf (fun j => fld 24 srcNinthYD.colsP j.val) i) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list is the checked transport of the Fifth short block. -/
theorem srcNinthY_short :
    shortCheckF srcNinthYD fifthSrcVec.sh.flat srcNinthYT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list has valid labels. -/
theorem srcNinthY_labels : srcNinthYT.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- Field bound for the packed word action. -/
theorem srcNinthY_growth : tensorWordGrowthAll srcNinthYWord * 64 < 2 ^ 128 := by
  decide +kernel

/-- The tensor block of the incoming representation. -/
theorem srcNinthYVec_ten :
    srcNinthYVec.ten =
      tensorRat 128 srcNinthYX ((tensorWordDenAll srcNinthYWord : ℚ) * 1) := rfl

/-- Bounds of the packed incoming tensor. -/
theorem srcNinthYX_bnd : TBnd 128 (tensorWordGrowthAll srcNinthYWord * 64) srcNinthYX :=
  (tensorWordAll_actual srcNinthYWord fifthSrcX_bnd srcNinthY_growth 1).1

/-- The short block of the incoming representation satisfies the range conditions. -/
theorem srcNinthYVec_ok : srcNinthYVec.sh.ok = true := ofList_ok _ srcNinthY_labels

/-- The incoming Ninth vector is represented exactly. -/
theorem srcNinthY_actual :
    griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis) =
      srcNinthYVec.real := by
  have hT := (tensorWordAll_actual srcNinthYWord fifthSrcX_bnd srcNinthY_growth 1).2
  have hT' : localTensorRepresentation
      (identWordFiber ((srcWordData srcNinthYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal fifthSrcVec.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 128 srcNinthYX ((tensorWordDenAll srcNinthYWord : ℚ) * 1)) := by
    rw [srcWordData_fst, fifthSrcVec_ten]
    exact hT
  have h := IdentVec.word_actual fifthSrcVec (srcWordData srcNinthYWord) srcNinthY_letters
    srcNinthYD srcNinthY_composite.1 srcNinthY_composite.2.1
    srcNinthY_composite.2.2 srcNinthYT
    srcNinthY_short _ hT' _ fifthSrc_actual
  rw [srcWordData_fst] at h
  rw [← srcNinthYWord_local]
  exact h

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
