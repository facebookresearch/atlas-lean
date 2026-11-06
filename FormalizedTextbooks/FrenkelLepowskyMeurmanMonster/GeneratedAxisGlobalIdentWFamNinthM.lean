/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth

/-! # Compact integer matrix glue for the Ninth source (goctad)

The factory's matrix parts evaluate transported integer blocks entrywise, at a kernel cost
proportional to the number of rank-one terms. `srcNinthMat` is written with 16 rank-one terms over
pair vectors; `srcNinthMatZc` is the same matrix (`srcNinthMat_toMat_eqZc`) with the 8 integer rank-
one terms of its block decomposition (coefficients over `16`), and `srcNinthMat_act_entryZc` gives
the entries of transported blocks from it. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Integer vector `0` of the compact Ninth block. -/
def srcNinthMatV0 : List ℤ :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]

/-- Integer vector `1` of the compact Ninth block. -/
def srcNinthMatV1 : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `2` of the compact Ninth block. -/
def srcNinthMatV2 : List ℤ :=
  [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `3` of the compact Ninth block. -/
def srcNinthMatV3 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]

/-- Integer vector `4` of the compact Ninth block. -/
def srcNinthMatV4 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Integer vector `5` of the compact Ninth block. -/
def srcNinthMatV5 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `6` of the compact Ninth block. -/
def srcNinthMatV6 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Integer vector `7` of the compact Ninth block. -/
def srcNinthMatV7 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]

/-- The Ninth source block as a compact integer block (8 rank-one terms over `16`). -/
def srcNinthMatZc : MatZ :=
  ⟨3 / 8, 16, [
    (-1, srcNinthMatV0),
    (-1, srcNinthMatV1),
    (-1, srcNinthMatV2),
    (-1, srcNinthMatV3),
    (-1, srcNinthMatV4),
    (-1, srcNinthMatV5),
    (-1, srcNinthMatV6),
    (-1, srcNinthMatV7)], 0⟩

set_option maxRecDepth 100000 in
/-- The Ninth source block and its compact integer block have the same matrix. -/
theorem srcNinthMat_toMat_eqZc : srcNinthMat.toMat = srcNinthMatZc.toRep.toMat := by
  ext i j
  rw [MatRep.toMat_apply, MatRep.toMat_apply]
  revert i j
  decide +kernel

/-- Entries of a transported Ninth source block from the compact integer block. -/
theorem srcNinthMat_act_entryZc (w : List IdentLetter) (i j : Fin 24) :
    (srcNinthMat.act identSpatialAlphabet w).entry i j = (srcNinthMatZc.act w).entry i j :=
  act_entry_of_toMat _ _ srcNinthMat_toMat_eqZc w i j

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
