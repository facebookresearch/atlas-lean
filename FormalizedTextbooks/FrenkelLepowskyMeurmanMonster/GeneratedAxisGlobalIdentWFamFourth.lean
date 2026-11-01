/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW

/-! # Factory glue for the Fourth source: integer matrix block -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent

/-- The vector `e_8 + s e_11`. -/
def fourthPairZ (s : ℤ) : List ℤ :=
  (List.range 24).map (fun j => if j = 8 then 1 else if j = 11 then s else 0)

/-- The Fourth source block as an integer block. -/
def fourthSrcMatZ : MatZ :=
  ⟨3 / 8, 8, [4, 5, 6, 7, 9, 10].map (fun i => (-2, unitListZ i)) ++
    [(-1, fourthPairZ 1), (3, fourthPairZ (-1))], 0⟩

set_option maxRecDepth 100000 in
/-- The Fourth source block and its integer block have the same matrix. -/
theorem fourthSrcMat_toMat_eqZ : fourthSrcMat.toMat = fourthSrcMatZ.toRep.toMat := by
  ext i j
  rw [MatRep.toMat_apply, MatRep.toMat_apply]
  revert i j
  decide +kernel

/-- Entries of a transported Fourth source block from integer data. -/
theorem fourthSrcMat_act_entryZ (w : List IdentLetter) (i j : Fin 24) :
    (fourthSrcMat.act identSpatialAlphabet w).entry i j = (fourthSrcMatZ.act w).entry i j :=
  act_entry_of_toMat _ _ fourthSrcMat_toMat_eqZ w i j

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
