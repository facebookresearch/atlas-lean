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

/-- Literal original-source and earlier-equation contexts replacing instruction 149130. -/
def y322TCIndexRepairRaw036 : List Y322RawContextEquationMove :=
  [
    ⟨84387, false, false,
      [],
      []⟩,
    ⟨87931, false, false,
      [],
      []⟩,
    ⟨90676, false, false,
      [],
      []⟩,
    ⟨88876, false, false,
      [6521, 8393],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed036 :
    ∀ move ∈ y322TCIndexRepairRaw036, move.Allowed 48648 226373 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149130. -/
theorem y322TCIndexRepairChecked036 :
    y322TCIndexRepairChecked ⟨149130, by decide⟩ y322TCIndexRepairRaw036
      y322TCIndexRepairAllowed036 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid036
    (hp : ∀ j : Fin 174819, j.val < 149130 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149130, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed036
    y322TCIndexRepairChecked036 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
