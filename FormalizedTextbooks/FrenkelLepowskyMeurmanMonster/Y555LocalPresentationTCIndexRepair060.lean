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

/-- Literal original-source and earlier-equation contexts replacing instruction 149291. -/
def y322TCIndexRepairRaw060 : List Y322RawContextEquationMove :=
  [
    ⟨77823, false, false,
      [],
      []⟩,
    ⟨77623, true, false,
      [],
      [7]⟩,
    ⟨77820, true, false,
      [154],
      [9, 7]⟩,
    ⟨77822, false, false,
      [154, 77215],
      []⟩,
    ⟨77817, false, false,
      [154],
      []⟩,
    ⟨77815, false, false,
      [154],
      []⟩,
    ⟨77781, false, false,
      [154],
      []⟩,
    ⟨77824, true, false,
      [],
      [77213]⟩,
    ⟨77824, true, false,
      [],
      [77213]⟩,
    ⟨77800, false, true,
      [],
      [77213]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed060 :
    ∀ move ∈ y322TCIndexRepairRaw060, move.Allowed 48648 226534 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149291. -/
theorem y322TCIndexRepairChecked060 :
    y322TCIndexRepairChecked ⟨149291, by decide⟩ y322TCIndexRepairRaw060
      y322TCIndexRepairAllowed060 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid060
    (hp : ∀ j : Fin 174819, j.val < 149291 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149291, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed060
    y322TCIndexRepairChecked060 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
