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

/-- Literal original-source and earlier-equation contexts replacing instruction 149379. -/
def y322TCIndexRepairRaw070 : List Y322RawContextEquationMove :=
  [
    ⟨77946, true, false,
      [],
      [15]⟩,
    ⟨77244, false, false,
      [77241],
      []⟩,
    ⟨77947, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed070 :
    ∀ move ∈ y322TCIndexRepairRaw070, move.Allowed 48648 226622 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149379. -/
theorem y322TCIndexRepairChecked070 :
    y322TCIndexRepairChecked ⟨149379, by decide⟩ y322TCIndexRepairRaw070
      y322TCIndexRepairAllowed070 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid070
    (hp : ∀ j : Fin 174819, j.val < 149379 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149379, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed070
    y322TCIndexRepairChecked070 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
