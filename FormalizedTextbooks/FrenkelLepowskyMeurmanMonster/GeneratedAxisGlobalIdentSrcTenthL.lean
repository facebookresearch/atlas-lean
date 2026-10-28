/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthY

/-! # The incoming Tenth vector with a literal matrix block

`srcTenthYL` is `srcTenthYVec` with its matrix block written out: the eight rank-one vectors are the
spatial images of the coordinate units `0, 1, 2, 3, 16, 17, 18, 19` under the Tenth source word,
each checked once by the kernel. `srcTenthYL_eq` identifies the two vectors, so later checks need
not re-evaluate the spatial word action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The spatial image of the coordinate unit `0` under the Tenth source word. -/
def srcTenthYV0 : List ℚ :=
  [(-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `0` is the literal vector. -/
theorem srcTenthYV0_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 0) = srcTenthYV0 := by
  decide +kernel

/-- The spatial image of the coordinate unit `1` under the Tenth source word. -/
def srcTenthYV1 : List ℚ :=
  [(-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `1` is the literal vector. -/
theorem srcTenthYV1_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 1) = srcTenthYV1 := by
  decide +kernel

/-- The spatial image of the coordinate unit `2` under the Tenth source word. -/
def srcTenthYV2 : List ℚ :=
  [(-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `2` is the literal vector. -/
theorem srcTenthYV2_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 2) = srcTenthYV2 := by
  decide +kernel

/-- The spatial image of the coordinate unit `3` under the Tenth source word. -/
def srcTenthYV3 : List ℚ :=
  [(-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `3` is the literal vector. -/
theorem srcTenthYV3_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 3) = srcTenthYV3 := by
  decide +kernel

/-- The spatial image of the coordinate unit `16` under the Tenth source word. -/
def srcTenthYV16 : List ℚ :=
  [(0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ),
    (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ),
    (1 / 2 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `16` is the literal vector. -/
theorem srcTenthYV16_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 16) = srcTenthYV16 := by
  decide +kernel

/-- The spatial image of the coordinate unit `17` under the Tenth source word. -/
def srcTenthYV17 : List ℚ :=
  [(0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `17` is the literal vector. -/
theorem srcTenthYV17_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 17) = srcTenthYV17 := by
  decide +kernel

/-- The spatial image of the coordinate unit `18` under the Tenth source word. -/
def srcTenthYV18 : List ℚ :=
  [(1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ),
    (0 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `18` is the literal vector. -/
theorem srcTenthYV18_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 18) = srcTenthYV18 := by
  decide +kernel

/-- The spatial image of the coordinate unit `19` under the Tenth source word. -/
def srcTenthYV19 : List ℚ :=
  [(1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `19` is the literal vector. -/
theorem srcTenthYV19_eq :
    spWordVec identSpatialAlphabet srcTenthYWord (unitList 19) = srcTenthYV19 := by
  decide +kernel

/-- The literal matrix block of the incoming Tenth vector. -/
def srcTenthYMat : MatRep :=
  ⟨1 / 4, [((1 / 4 : ℚ), srcTenthYV0), ((1 / 4 : ℚ), srcTenthYV1), ((1 / 4 : ℚ), srcTenthYV2),
    ((1 / 4 : ℚ), srcTenthYV3), ((1 / 4 : ℚ), srcTenthYV16), ((1 / 4 : ℚ), srcTenthYV17),
    ((1 / 4 : ℚ), srcTenthYV18), ((1 / 4 : ℚ), srcTenthYV19)]⟩

/-- The transported matrix block is the literal one. -/
theorem srcTenthYMat_eq :
    fifthSrcMat.act identSpatialAlphabet srcTenthYWord = srcTenthYMat := by
  change (⟨1 / 4, [
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 0)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 1)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 2)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 3)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 16)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 17)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 18)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcTenthYWord (unitList 19))]⟩ :
    MatRep) = _
  rw [srcTenthYV0_eq]
  rw [srcTenthYV1_eq]
  rw [srcTenthYV2_eq]
  rw [srcTenthYV3_eq]
  rw [srcTenthYV16_eq]
  rw [srcTenthYV17_eq]
  rw [srcTenthYV18_eq]
  rw [srcTenthYV19_eq]
  rfl

/-- The incoming Tenth vector with the literal matrix block. -/
def srcTenthYL : IdentVec :=
  ⟨srcTenthYMat, ShortData.ofList srcTenthYT, 1 / 16,
    tensorRat 128 srcTenthYX ((tensorWordDenAll srcTenthYWord : ℚ) * 1)⟩

/-- The literal-matrix vector is the word image vector. -/
theorem srcTenthYL_eq : srcTenthYL = srcTenthYVec := by
  unfold srcTenthYL srcTenthYVec
  rw [srcTenthYMat_eq]

/-- The literal-matrix vector represents the incoming vector. -/
theorem srcTenthYL_actual :
    griessConwayEncode
      (rhoLocal generatedTenthLocal generatedFifthAxis) =
      srcTenthYL.real := by
  rw [srcTenthYL_eq]
  exact srcTenthY_actual

/-- The short block of the literal-matrix vector satisfies the range conditions. -/
theorem srcTenthYL_ok : srcTenthYL.sh.ok = true := by
  rw [srcTenthYL_eq]
  exact srcTenthYVec_ok

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
