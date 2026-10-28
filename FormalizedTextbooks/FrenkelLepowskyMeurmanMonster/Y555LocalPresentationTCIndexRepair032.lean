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

/-- Literal original-source and earlier-equation contexts replacing instruction 149108. -/
def y322TCIndexRepairRaw032 : List Y322RawContextEquationMove :=
  [
    ⟨77561, true, false,
      [],
      [1]⟩,
    ⟨77251, false, false,
      [77163],
      []⟩,
    ⟨77562, false, false,
      [],
      []⟩,
    ⟨77660, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed032 :
    ∀ move ∈ y322TCIndexRepairRaw032, move.Allowed 48648 226351 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149108. -/
theorem y322TCIndexRepairChecked032 :
    y322TCIndexRepairChecked ⟨149108, by decide⟩ y322TCIndexRepairRaw032
      y322TCIndexRepairAllowed032 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid032
    (hp : ∀ j : Fin 174819, j.val < 149108 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149108, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed032
    y322TCIndexRepairChecked032 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
