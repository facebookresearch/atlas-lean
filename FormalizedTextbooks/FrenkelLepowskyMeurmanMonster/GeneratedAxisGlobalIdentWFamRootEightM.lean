/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight

/-! # Compact integer matrix glue for the Root8 source (goctad)

The factory's matrix parts evaluate transported integer blocks entrywise, at a kernel cost
proportional to the number of rank-one terms. `srcRootEightMat` is written with 49 rank-one terms
over pair vectors; `srcRootEightMatZc` is the same matrix (`srcRootEightMat_toMat_eqZc`) with the 2
integer rank-one terms of its block decomposition (coefficients over `16`), and
`srcRootEightMat_act_entryZc` gives the entries of transported blocks from it. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Integer vector `0` of the compact Root8 block. -/
def srcRootEightMatV0 : List ℤ :=
  [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0]

/-- Integer vector `1` of the compact Root8 block. -/
def srcRootEightMatV1 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]

/-- The Root8 source block as a compact integer block (2 rank-one terms over `16`). -/
def srcRootEightMatZc : MatZ :=
  ⟨5 / 16, 16, [(1, srcRootEightMatV0), (-1, srcRootEightMatV1)], 0⟩

set_option maxRecDepth 100000 in
/-- The Root8 source block and its compact integer block have the same matrix. -/
theorem srcRootEightMat_toMat_eqZc : srcRootEightMat.toMat = srcRootEightMatZc.toRep.toMat := by
  ext i j
  rw [MatRep.toMat_apply, MatRep.toMat_apply]
  revert i j
  decide +kernel

/-- Entries of a transported Root8 source block from the compact integer block. -/
theorem srcRootEightMat_act_entryZc (w : List IdentLetter) (i j : Fin 24) :
    (srcRootEightMat.act identSpatialAlphabet w).entry i j = (srcRootEightMatZc.act w).entry i j :=
  act_entry_of_toMat _ _ srcRootEightMat_toMat_eqZc w i j

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
