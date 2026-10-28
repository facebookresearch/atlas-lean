/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth

/-! # Compact integer matrix glue for the Tenth source (goctad)

The factory's matrix parts evaluate transported integer blocks entrywise, at a kernel cost
proportional to the number of rank-one terms. `srcTenthMat` is written with 22 rank-one terms over
pair vectors; `srcTenthMatZc` is the same matrix (`srcTenthMat_toMat_eqZc`) with the 8 integer rank-
one terms of its block decomposition (coefficients over `16`), and `srcTenthMat_act_entryZc` gives
the entries of transported blocks from it. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Integer vector `0` of the compact Tenth block. -/
def srcTenthMatV0 : List ℤ :=
  [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `1` of the compact Tenth block. -/
def srcTenthMatV1 : List ℤ :=
  [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `2` of the compact Tenth block. -/
def srcTenthMatV2 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `3` of the compact Tenth block. -/
def srcTenthMatV3 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `4` of the compact Tenth block. -/
def srcTenthMatV4 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]

/-- Integer vector `5` of the compact Tenth block. -/
def srcTenthMatV5 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0]

/-- Integer vector `6` of the compact Tenth block. -/
def srcTenthMatV6 : List ℤ :=
  [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1]

/-- Integer vector `7` of the compact Tenth block. -/
def srcTenthMatV7 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]

/-- The Tenth source block as a compact integer block (8 rank-one terms over `16`). -/
def srcTenthMatZc : MatZ :=
  ⟨9 / 32, 16, [
    (1, srcTenthMatV0),
    (1, srcTenthMatV1),
    (1, srcTenthMatV2),
    (1, srcTenthMatV3),
    (1, srcTenthMatV4),
    (1, srcTenthMatV5),
    (1, srcTenthMatV6),
    (1, srcTenthMatV7)], 0⟩

set_option maxRecDepth 100000 in
/-- The Tenth source block and its compact integer block have the same matrix. -/
theorem srcTenthMat_toMat_eqZc : srcTenthMat.toMat = srcTenthMatZc.toRep.toMat := by
  ext i j
  rw [MatRep.toMat_apply, MatRep.toMat_apply]
  revert i j
  decide +kernel

/-- Entries of a transported Tenth source block from the compact integer block. -/
theorem srcTenthMat_act_entryZc (w : List IdentLetter) (i j : Fin 24) :
    (srcTenthMat.act identSpatialAlphabet w).entry i j = (srcTenthMatZc.act w).entry i j :=
  act_entry_of_toMat _ _ srcTenthMat_toMat_eqZc w i j

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
