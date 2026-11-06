/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightY

/-! # The incoming Root8 vector with a literal matrix block

`srcRootEightYL` is `srcRootEightYVec` with its matrix block written out: the eight rank-one vectors
are the spatial images of the coordinate units `0, 1, 2, 3, 16, 17, 18, 19` under the Root8 source
word, each checked once by the kernel. `srcRootEightYL_eq` identifies the two vectors, so later
checks need not re-evaluate the spatial word action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The spatial image of the coordinate unit `0` under the Root8 source word. -/
def srcRootEightYV0 : List ℚ :=
  [(0 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `0` is the literal vector. -/
theorem srcRootEightYV0_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 0) = srcRootEightYV0 := by
  decide +kernel

/-- The spatial image of the coordinate unit `1` under the Root8 source word. -/
def srcRootEightYV1 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `1` is the literal vector. -/
theorem srcRootEightYV1_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 1) = srcRootEightYV1 := by
  decide +kernel

/-- The spatial image of the coordinate unit `2` under the Root8 source word. -/
def srcRootEightYV2 : List ℚ :=
  [(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `2` is the literal vector. -/
theorem srcRootEightYV2_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 2) = srcRootEightYV2 := by
  decide +kernel

/-- The spatial image of the coordinate unit `3` under the Root8 source word. -/
def srcRootEightYV3 : List ℚ :=
  [(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `3` is the literal vector. -/
theorem srcRootEightYV3_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 3) = srcRootEightYV3 := by
  decide +kernel

/-- The spatial image of the coordinate unit `16` under the Root8 source word. -/
def srcRootEightYV16 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 2 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `16` is the literal vector. -/
theorem srcRootEightYV16_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 16) = srcRootEightYV16 := by
  decide +kernel

/-- The spatial image of the coordinate unit `17` under the Root8 source word. -/
def srcRootEightYV17 : List ℚ :=
  [(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ),
    (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `17` is the literal vector. -/
theorem srcRootEightYV17_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 17) = srcRootEightYV17 := by
  decide +kernel

/-- The spatial image of the coordinate unit `18` under the Root8 source word. -/
def srcRootEightYV18 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ),
    (0 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `18` is the literal vector. -/
theorem srcRootEightYV18_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 18) = srcRootEightYV18 := by
  decide +kernel

/-- The spatial image of the coordinate unit `19` under the Root8 source word. -/
def srcRootEightYV19 : List ℚ :=
  [(1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ),
    (-1 / 4 : ℚ), (1 / 4 : ℚ)]

set_option maxRecDepth 100000 in
/-- The spatial image of the coordinate unit `19` is the literal vector. -/
theorem srcRootEightYV19_eq :
    spWordVec identSpatialAlphabet srcRootEightYWord (unitList 19) = srcRootEightYV19 := by
  decide +kernel

/-- The literal matrix block of the incoming Root8 vector. -/
def srcRootEightYMat : MatRep :=
  ⟨1 / 4, [((1 / 4 : ℚ), srcRootEightYV0), ((1 / 4 : ℚ), srcRootEightYV1),
    ((1 / 4 : ℚ), srcRootEightYV2), ((1 / 4 : ℚ), srcRootEightYV3),
    ((1 / 4 : ℚ), srcRootEightYV16), ((1 / 4 : ℚ), srcRootEightYV17),
    ((1 / 4 : ℚ), srcRootEightYV18), ((1 / 4 : ℚ), srcRootEightYV19)]⟩

/-- The transported matrix block is the literal one. -/
theorem srcRootEightYMat_eq :
    fifthSrcMat.act identSpatialAlphabet srcRootEightYWord = srcRootEightYMat := by
  change (⟨1 / 4, [
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 0)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 1)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 2)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 3)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 16)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 17)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 18)),
    ((1 / 4 : ℚ), spWordVec identSpatialAlphabet srcRootEightYWord (unitList 19))]⟩ :
    MatRep) = _
  rw [srcRootEightYV0_eq]
  rw [srcRootEightYV1_eq]
  rw [srcRootEightYV2_eq]
  rw [srcRootEightYV3_eq]
  rw [srcRootEightYV16_eq]
  rw [srcRootEightYV17_eq]
  rw [srcRootEightYV18_eq]
  rw [srcRootEightYV19_eq]
  rfl

/-- The incoming Root8 vector with the literal matrix block. -/
def srcRootEightYL : IdentVec :=
  ⟨srcRootEightYMat, ShortData.ofList srcRootEightYT, 1 / 16,
    tensorRat 128 srcRootEightYX ((tensorWordDenAll srcRootEightYWord : ℚ) * 1)⟩

/-- The literal-matrix vector is the word image vector. -/
theorem srcRootEightYL_eq : srcRootEightYL = srcRootEightYVec := by
  unfold srcRootEightYL srcRootEightYVec
  rw [srcRootEightYMat_eq]

/-- The literal-matrix vector represents the incoming vector. -/
theorem srcRootEightYL_actual :
    griessConwayEncode
      (rhoLocal generatedFifthRootEightLocal generatedFifthAxis) =
      srcRootEightYL.real := by
  rw [srcRootEightYL_eq]
  exact srcRootEightY_actual

/-- The short block of the literal-matrix vector satisfies the range conditions. -/
theorem srcRootEightYL_ok : srcRootEightYL.sh.ok = true := by
  rw [srcRootEightYL_eq]
  exact srcRootEightYVec_ok

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
