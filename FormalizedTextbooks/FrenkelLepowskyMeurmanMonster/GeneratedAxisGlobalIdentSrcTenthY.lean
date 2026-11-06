/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource

/-! # The incoming Tenth vector as an identification vector

The Tenth axis is `sExtra y` for the local image `y` of the Fifth axis under the
Tenth source word. `srcTenthYVec` represents `y` exactly (`srcTenthY_actual`): the
word image of `fifthSrcVec`, with the letter data, the composite mask data and the short image
list certified by the kernel, the matrix block by the spatial alphabet and the tensor block by
the packed word action `tensorWordAll`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The packed tensor of the incoming Tenth vector. -/
def srcTenthYX : List SVec := tensorWordAll 128 srcTenthYWord fifthSrcX

/-- The incoming Tenth vector as an identification vector. -/
noncomputable def srcTenthYVec : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet srcTenthYWord, ShortData.ofList srcTenthYT, 1 / 16,
    tensorRat 128 srcTenthYX ((tensorWordDenAll srcTenthYWord : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the Tenth source word are certified. -/
theorem srcTenthY_letters :
    (srcWordData srcTenthYWord).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite mask data of the Tenth source word are certified. -/
theorem srcTenthY_composite : srcTenthYD.ok = true ∧
    (∀ i : Fin 24, qmWordP ((srcWordData srcTenthYWord).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 srcTenthYD.colsP i.val, srcTenthYD.coeff.testBit i.val)) ∧
    (∀ i : Fin 24,
      fld 24 srcTenthYD.rowsP i.val =
        rowsOf (fun j => fld 24 srcTenthYD.colsP j.val) i) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list is the checked transport of the Fifth short block. -/
theorem srcTenthY_short :
    shortCheckF srcTenthYD fifthSrcVec.sh.flat srcTenthYT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list has valid labels. -/
theorem srcTenthY_labels : srcTenthYT.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- Field bound for the packed word action. -/
theorem srcTenthY_growth : tensorWordGrowthAll srcTenthYWord * 64 < 2 ^ 128 := by
  decide +kernel

/-- The tensor block of the incoming representation. -/
theorem srcTenthYVec_ten :
    srcTenthYVec.ten =
      tensorRat 128 srcTenthYX ((tensorWordDenAll srcTenthYWord : ℚ) * 1) := rfl

/-- Bounds of the packed incoming tensor. -/
theorem srcTenthYX_bnd : TBnd 128 (tensorWordGrowthAll srcTenthYWord * 64) srcTenthYX :=
  (tensorWordAll_actual srcTenthYWord fifthSrcX_bnd srcTenthY_growth 1).1

/-- The short block of the incoming representation satisfies the range conditions. -/
theorem srcTenthYVec_ok : srcTenthYVec.sh.ok = true := ofList_ok _ srcTenthY_labels

/-- The incoming Tenth vector is represented exactly. -/
theorem srcTenthY_actual :
    griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis) =
      srcTenthYVec.real := by
  have hT := (tensorWordAll_actual srcTenthYWord fifthSrcX_bnd srcTenthY_growth 1).2
  have hT' : localTensorRepresentation
      (identWordFiber ((srcWordData srcTenthYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal fifthSrcVec.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 128 srcTenthYX ((tensorWordDenAll srcTenthYWord : ℚ) * 1)) := by
    rw [srcWordData_fst, fifthSrcVec_ten]
    exact hT
  have h := IdentVec.word_actual fifthSrcVec (srcWordData srcTenthYWord) srcTenthY_letters
    srcTenthYD srcTenthY_composite.1 srcTenthY_composite.2.1
    srcTenthY_composite.2.2 srcTenthYT
    srcTenthY_short _ hT' _ fifthSrc_actual
  rw [srcWordData_fst] at h
  rw [← srcTenthYWord_local]
  exact h

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
