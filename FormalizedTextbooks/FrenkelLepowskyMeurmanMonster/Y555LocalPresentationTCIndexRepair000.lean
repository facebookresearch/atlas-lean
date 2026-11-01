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

/-- Literal original-source and earlier-equation contexts replacing instruction 148825. -/
def y322TCIndexRepairRaw000 : List Y322RawContextEquationMove :=
  [
    ⟨38616, true, false,
      [],
      []⟩,
    ⟨77338, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed000 :
    ∀ move ∈ y322TCIndexRepairRaw000, move.Allowed 48648 226068 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148825. -/
theorem y322TCIndexRepairChecked000 :
    y322TCIndexRepairChecked ⟨148825, by decide⟩ y322TCIndexRepairRaw000
      y322TCIndexRepairAllowed000 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid000
    (hp : ∀ j : Fin 174819, j.val < 148825 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148825, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed000
    y322TCIndexRepairChecked000 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
