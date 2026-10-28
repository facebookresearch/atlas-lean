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

/-- Literal original-source and earlier-equation contexts replacing instruction 149829. -/
def y322TCIndexRepairRaw127 : List Y322RawContextEquationMove :=
  [
    ⟨92798, false, false,
      [],
      []⟩,
    ⟨92800, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed127 :
    ∀ move ∈ y322TCIndexRepairRaw127, move.Allowed 48648 227072 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149829. -/
theorem y322TCIndexRepairChecked127 :
    y322TCIndexRepairChecked ⟨149829, by decide⟩ y322TCIndexRepairRaw127
      y322TCIndexRepairAllowed127 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid127
    (hp : ∀ j : Fin 174819, j.val < 149829 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149829, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed127
    y322TCIndexRepairChecked127 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
