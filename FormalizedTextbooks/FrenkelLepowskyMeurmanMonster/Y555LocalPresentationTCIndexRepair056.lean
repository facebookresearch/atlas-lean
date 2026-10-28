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

/-- Literal original-source and earlier-equation contexts replacing instruction 149261. -/
def y322TCIndexRepairRaw056 : List Y322RawContextEquationMove :=
  [
    ⟨79916, false, false,
      [955],
      []⟩,
    ⟨79920, false, false,
      [955, 969],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed056 :
    ∀ move ∈ y322TCIndexRepairRaw056, move.Allowed 48648 226504 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149261. -/
theorem y322TCIndexRepairChecked056 :
    y322TCIndexRepairChecked ⟨149261, by decide⟩ y322TCIndexRepairRaw056
      y322TCIndexRepairAllowed056 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid056
    (hp : ∀ j : Fin 174819, j.val < 149261 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149261, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed056
    y322TCIndexRepairChecked056 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
