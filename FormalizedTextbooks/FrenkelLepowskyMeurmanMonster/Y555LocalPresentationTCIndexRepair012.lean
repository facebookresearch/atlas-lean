/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact replacement of one incorrectly reused prior-source instruction. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepairContexts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Literal original-source and earlier-equation contexts replacing instruction 148940. -/
def y322TCIndexRepairRaw012 : List Y322RawContextEquationMove :=
  [
    ⟨81037, false, false,
      [],
      []⟩,
    ⟨89925, false, false,
      [1423],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed012 :
    ∀ move ∈ y322TCIndexRepairRaw012, move.Allowed 48648 226183 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148940. -/
theorem y322TCIndexRepairChecked012 :
    y322TCIndexRepairChecked ⟨148940, by decide⟩ y322TCIndexRepairRaw012
      y322TCIndexRepairAllowed012 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid012
    (hp : ∀ j : Fin 174819, j.val < 148940 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148940, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed012
    y322TCIndexRepairChecked012 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
