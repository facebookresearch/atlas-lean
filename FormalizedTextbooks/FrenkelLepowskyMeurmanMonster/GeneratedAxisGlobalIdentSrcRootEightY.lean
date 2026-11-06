/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource

/-! # The incoming Root8 vector as an identification vector

The Root8 axis is `sExtra y` for the local image `y` of the Fifth axis under the
Root8 source word. `srcRootEightYVec` represents `y` exactly (`srcRootEightY_actual`): the
word image of `fifthSrcVec`, with the letter data, the composite mask data and the short image
list certified by the kernel, the matrix block by the spatial alphabet and the tensor block by
the packed word action `tensorWordAll`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The packed tensor of the incoming Root8 vector. -/
def srcRootEightYX : List SVec := tensorWordAll 128 srcRootEightYWord fifthSrcX

/-- The incoming Root8 vector as an identification vector. -/
noncomputable def srcRootEightYVec : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet srcRootEightYWord, ShortData.ofList srcRootEightYT, 1 / 16,
    tensorRat 128 srcRootEightYX ((tensorWordDenAll srcRootEightYWord : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the Root8 source word are certified. -/
theorem srcRootEightY_letters :
    (srcWordData srcRootEightYWord).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite mask data of the Root8 source word are certified. -/
theorem srcRootEightY_composite : srcRootEightYD.ok = true ∧
    (∀ i : Fin 24, qmWordP ((srcWordData srcRootEightYWord).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 srcRootEightYD.colsP i.val, srcRootEightYD.coeff.testBit i.val)) ∧
    (∀ i : Fin 24,
      fld 24 srcRootEightYD.rowsP i.val =
        rowsOf (fun j => fld 24 srcRootEightYD.colsP j.val) i) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list is the checked transport of the Fifth short block. -/
theorem srcRootEightY_short :
    shortCheckF srcRootEightYD fifthSrcVec.sh.flat srcRootEightYT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short image list has valid labels. -/
theorem srcRootEightY_labels : srcRootEightYT.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- Field bound for the packed word action. -/
theorem srcRootEightY_growth : tensorWordGrowthAll srcRootEightYWord * 64 < 2 ^ 128 := by
  decide +kernel

/-- The tensor block of the incoming representation. -/
theorem srcRootEightYVec_ten :
    srcRootEightYVec.ten =
      tensorRat 128 srcRootEightYX ((tensorWordDenAll srcRootEightYWord : ℚ) * 1) := rfl

/-- Bounds of the packed incoming tensor. -/
theorem srcRootEightYX_bnd : TBnd 128 (tensorWordGrowthAll srcRootEightYWord * 64) srcRootEightYX :=
  (tensorWordAll_actual srcRootEightYWord fifthSrcX_bnd srcRootEightY_growth 1).1

/-- The short block of the incoming representation satisfies the range conditions. -/
theorem srcRootEightYVec_ok : srcRootEightYVec.sh.ok = true := ofList_ok _ srcRootEightY_labels

/-- The incoming Root8 vector is represented exactly. -/
theorem srcRootEightY_actual :
    griessConwayEncode (rhoLocal generatedFifthRootEightLocal generatedFifthAxis) =
      srcRootEightYVec.real := by
  have hT := (tensorWordAll_actual srcRootEightYWord fifthSrcX_bnd srcRootEightY_growth 1).2
  have hT' : localTensorRepresentation
      (identWordFiber ((srcWordData srcRootEightYWord).map Prod.fst))
      (generatedAxisGlobalRationalTensorReal fifthSrcVec.ten) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat 128 srcRootEightYX ((tensorWordDenAll srcRootEightYWord : ℚ) * 1)) := by
    rw [srcWordData_fst, fifthSrcVec_ten]
    exact hT
  have h := IdentVec.word_actual fifthSrcVec (srcWordData srcRootEightYWord) srcRootEightY_letters
    srcRootEightYD srcRootEightY_composite.1 srcRootEightY_composite.2.1
    srcRootEightY_composite.2.2 srcRootEightYT
    srcRootEightY_short _ hT' _ fifthSrc_actual
  rw [srcWordData_fst] at h
  rw [← srcRootEightYWord_local]
  exact h

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
