/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcNinthY

/-! # The incoming Ninth vector with a literal matrix block

`srcNinthYL` is `srcNinthYVec` with its matrix block written out: the eight rank-one vectors are the
spatial images of the coordinate units `0, 1, 2, 3, 16, 17, 18, 19` under the Ninth source word,
each checked once by the kernel. `srcNinthYL_eq` identifies the two vectors, so later checks need
not re-evaluate the spatial word action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The spatial image of the coordinate unit `0` under the Ninth source word. -/
def srcNinthYV0 : List ℚ :=
  [(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ),
    (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `0` is the literal vector. -/
theorem srcNinthYV0_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 0) = srcNinthYV0 := by
  decide +kernel

/-- The spatial image of the coordinate unit `1` under the Ninth source word. -/
def srcNinthYV1 : List ℚ :=
  [(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `1` is the literal vector. -/
theorem srcNinthYV1_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 1) = srcNinthYV1 := by
  decide +kernel

/-- The spatial image of the coordinate unit `2` under the Ninth source word. -/
def srcNinthYV2 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ),
    (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `2` is the literal vector. -/
theorem srcNinthYV2_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 2) = srcNinthYV2 := by
  decide +kernel

/-- The spatial image of the coordinate unit `3` under the Ninth source word. -/
def srcNinthYV3 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ),
    (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (0 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `3` is the literal vector. -/
theorem srcNinthYV3_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 3) = srcNinthYV3 := by
  decide +kernel

/-- The spatial image of the coordinate unit `16` under the Ninth source word. -/
def srcNinthYV16 : List ℚ :=
  [(-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `16` is the literal vector. -/
theorem srcNinthYV16_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 16) = srcNinthYV16 := by
  decide +kernel

/-- The spatial image of the coordinate unit `17` under the Ninth source word. -/
def srcNinthYV17 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `17` is the literal vector. -/
theorem srcNinthYV17_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 17) = srcNinthYV17 := by
  decide +kernel

/-- The spatial image of the coordinate unit `18` under the Ninth source word. -/
def srcNinthYV18 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 2 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `18` is the literal vector. -/
theorem srcNinthYV18_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 18) = srcNinthYV18 := by
  decide +kernel

/-- The spatial image of the coordinate unit `19` under the Ninth source word. -/
def srcNinthYV19 : List ℚ :=
  [(1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ),
    (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `19` is the literal vector. -/
theorem srcNinthYV19_eq :
    spWordVec identSpatialAlphabet srcNinthYWord (unitList 19) = srcNinthYV19 := by
  decide +kernel

/-- The literal matrix block of the incoming Ninth vector. -/
def srcNinthYMat : MatRep :=
  ⟨1 / 4, [((1 / 4 : ℚ), srcNinthYV0), ((1 / 4 : ℚ), srcNinthYV1), ((1 / 4 : ℚ), srcNinthYV2),
    ((1 / 4 : ℚ), srcNinthYV3), ((1 / 4 : ℚ), srcNinthYV16), ((1 / 4 : ℚ), srcNinthYV17),
    ((1 / 4 : ℚ), srcNinthYV18), ((1 / 4 : ℚ), srcNinthYV19)]⟩

/-- The transported matrix block is the literal one. -/
theorem srcNinthYMat_eq :
    fifthSrcMat.act identSpatialAlphabet srcNinthYWord = srcNinthYMat := by
  change (⟨1 / 4, [
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 0)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 1)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 2)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 3)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 16)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 17)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 18)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcNinthYWord (unitList 19))]⟩ :
    MatRep) = _
  rw [srcNinthYV0_eq]
  rw [srcNinthYV1_eq]
  rw [srcNinthYV2_eq]
  rw [srcNinthYV3_eq]
  rw [srcNinthYV16_eq]
  rw [srcNinthYV17_eq]
  rw [srcNinthYV18_eq]
  rw [srcNinthYV19_eq]
  rfl

/-- The incoming Ninth vector with the literal matrix block. -/
def srcNinthYL : IdentVec :=
  ⟨srcNinthYMat, ShortData.ofList srcNinthYT, 1 / 16,
    tensorRat 128 srcNinthYX ((tensorWordDenAll srcNinthYWord : ℚ) * 1)⟩

/-- The literal-matrix vector is the word image vector. -/
theorem srcNinthYL_eq : srcNinthYL = srcNinthYVec := by
  unfold srcNinthYL srcNinthYVec
  rw [srcNinthYMat_eq]

/-- The literal-matrix vector represents the incoming vector. -/
theorem srcNinthYL_actual :
    griessConwayEncode
      (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis) =
      srcNinthYL.real := by
  rw [srcNinthYL_eq]
  exact srcNinthY_actual

/-- The short block of the literal-matrix vector satisfies the range conditions. -/
theorem srcNinthYL_ok : srcNinthYL.sh.ok = true := by
  rw [srcNinthYL_eq]
  exact srcNinthYVec_ok

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
