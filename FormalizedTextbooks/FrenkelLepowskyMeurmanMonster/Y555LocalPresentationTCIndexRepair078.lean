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

/-- Literal original-source and earlier-equation contexts replacing instruction 149463. -/
def y322TCIndexRepairRaw078 : List Y322RawContextEquationMove :=
  [
    ⟨83360, false, false,
      [],
      []⟩,
    ⟨83357, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed078 :
    ∀ move ∈ y322TCIndexRepairRaw078, move.Allowed 48648 226706 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149463. -/
theorem y322TCIndexRepairChecked078 :
    y322TCIndexRepairChecked ⟨149463, by decide⟩ y322TCIndexRepairRaw078
      y322TCIndexRepairAllowed078 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid078
    (hp : ∀ j : Fin 174819, j.val < 149463 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149463, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed078
    y322TCIndexRepairChecked078 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
