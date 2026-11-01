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

/-- Literal original-source and earlier-equation contexts replacing instruction 149773. -/
def y322TCIndexRepairRaw120 : List Y322RawContextEquationMove :=
  [
    ⟨78548, false, false,
      [],
      []⟩,
    ⟨78539, true, false,
      [],
      [15]⟩,
    ⟨77448, false, false,
      [77371],
      []⟩,
    ⟨77449, false, false,
      [77371],
      []⟩,
    ⟨78545, false, false,
      [],
      [9]⟩,
    ⟨78535, false, false,
      [329],
      []⟩,
    ⟨78546, false, false,
      [],
      []⟩,
    ⟨78547, false, false,
      [],
      []⟩,
    ⟨78544, false, false,
      [329],
      []⟩,
    ⟨78480, true, false,
      [],
      [77373]⟩,
    ⟨78546, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed120 :
    ∀ move ∈ y322TCIndexRepairRaw120, move.Allowed 48648 227016 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149773. -/
theorem y322TCIndexRepairChecked120 :
    y322TCIndexRepairChecked ⟨149773, by decide⟩ y322TCIndexRepairRaw120
      y322TCIndexRepairAllowed120 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid120
    (hp : ∀ j : Fin 174819, j.val < 149773 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149773, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed120
    y322TCIndexRepairChecked120 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
