/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWTight

/-! # Factory base: integer matrix data from matrix equality

`act_entry_of_toMat`: if a source matrix block has the same matrix as an integer block, the
entries of every transported block are the entries of the transported integer block (the matrix
action determines the transported matrix). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-- Entries of a transported block from an integer block with the same matrix. -/
theorem act_entry_of_toMat (A : MatRep) (M : MatZ) (h : A.toMat = M.toRep.toMat)
    (w : List IdentLetter) (i j : Fin 24) :
    (A.act identSpatialAlphabet w).entry i j = (M.act w).entry i j := by
  rw [← MatZ.act_entry, ← MatRep.toMat_apply, ← MatRep.toMat_apply]
  have h1 := identWord_matrix w A
  have h2 := identWord_matrix w M.toRep
  rw [h, h2] at h1
  have h3 := congrFun (congrFun h1 i) j
  simp only [matR, Matrix.map_apply] at h3
  exact ((Rat.castHom ℝ).injective h3).symm

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
