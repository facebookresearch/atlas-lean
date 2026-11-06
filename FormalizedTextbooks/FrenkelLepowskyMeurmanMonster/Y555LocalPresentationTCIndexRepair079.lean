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

/-- Literal original-source and earlier-equation contexts replacing instruction 149465. -/
def y322TCIndexRepairRaw079 : List Y322RawContextEquationMove :=
  [
    ⟨77983, false, false,
      [],
      []⟩,
    ⟨78987, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed079 :
    ∀ move ∈ y322TCIndexRepairRaw079, move.Allowed 48648 226708 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149465. -/
theorem y322TCIndexRepairChecked079 :
    y322TCIndexRepairChecked ⟨149465, by decide⟩ y322TCIndexRepairRaw079
      y322TCIndexRepairAllowed079 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid079
    (hp : ∀ j : Fin 174819, j.val < 149465 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149465, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed079
    y322TCIndexRepairChecked079 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
