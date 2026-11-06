/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcEighth

/-! # The Eighth source matrix block as an integer block

`e8SrcMatZ` is the matrix block of the Eighth source (`srcEighthMat`, diagonal `3/8`, `1/4`,
`3/4`) as an integer block; `e8SrcMat_act_entryZ` evaluates the matrix block of a transported
source from integer data, for the integer matrix and pair parts of the pairing (`triMatF_eq_ZI`,
`pairSumQ_eq_ZI`; rational arithmetic is slow in the kernel when there are many pair terms). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Eighth source block as an integer block (numerators over `8`). -/
def e8SrcMatZ : MatZ :=
  ⟨0, 8, [(3, unitListZ 0), (3, unitListZ 1), (3, unitListZ 2), (3, unitListZ 3),
    (2, unitListZ 4), (3, unitListZ 5), (3, unitListZ 6), (2, unitListZ 7), (2, unitListZ 8),
    (3, unitListZ 9), (3, unitListZ 10), (2, unitListZ 11), (2, unitListZ 12), (2, unitListZ 13),
    (2, unitListZ 14), (2, unitListZ 15), (3, unitListZ 16), (2, unitListZ 17), (3, unitListZ 18),
    (2, unitListZ 19), (6, unitListZ 20), (2, unitListZ 21), (3, unitListZ 22),
    (3, unitListZ 23)], 0⟩

set_option maxRecDepth 100000 in
/-- The Eighth source block and its integer block have the same matrix. -/
theorem e8SrcMat_toMat_eqZ : srcEighthMat.toMat = e8SrcMatZ.toRep.toMat := by
  ext i j
  rw [MatRep.toMat_apply, MatRep.toMat_apply]
  revert i j
  decide +kernel

/-- Entries of a transported Eighth source block from integer data. -/
theorem e8SrcMat_act_entryZ (w : List IdentLetter) (i j : Fin 24) :
    (srcEighthMat.act identSpatialAlphabet w).entry i j = (e8SrcMatZ.act w).entry i j := by
  rw [← MatZ.act_entry, ← MatRep.toMat_apply, ← MatRep.toMat_apply]
  have h1 := identWord_matrix w srcEighthMat
  have h2 := identWord_matrix w e8SrcMatZ.toRep
  rw [e8SrcMat_toMat_eqZ, h2] at h1
  have h3 := congrFun (congrFun h1 i) j
  simp only [matR, Matrix.map_apply] at h3
  exact ((Rat.castHom ℝ).injective h3).symm

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
