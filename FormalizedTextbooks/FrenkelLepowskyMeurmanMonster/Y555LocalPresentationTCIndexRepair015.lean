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

/-- Literal original-source and earlier-equation contexts replacing instruction 148975. -/
def y322TCIndexRepairRaw015 : List Y322RawContextEquationMove :=
  [
    ⟨88989, false, false,
      [],
      []⟩,
    ⟨90626, false, false,
      [8777],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed015 :
    ∀ move ∈ y322TCIndexRepairRaw015, move.Allowed 48648 226218 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148975. -/
theorem y322TCIndexRepairChecked015 :
    y322TCIndexRepairChecked ⟨148975, by decide⟩ y322TCIndexRepairRaw015
      y322TCIndexRepairAllowed015 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid015
    (hp : ∀ j : Fin 174819, j.val < 148975 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148975, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed015
    y322TCIndexRepairChecked015 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
