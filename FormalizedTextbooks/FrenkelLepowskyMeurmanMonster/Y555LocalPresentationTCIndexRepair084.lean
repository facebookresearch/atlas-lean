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

/-- Literal original-source and earlier-equation contexts replacing instruction 149500. -/
def y322TCIndexRepairRaw084 : List Y322RawContextEquationMove :=
  [
    ⟨78000, true, false,
      [],
      []⟩,
    ⟨90506, true, false,
      [11878],
      [1]⟩,
    ⟨79079, false, false,
      [11878],
      []⟩,
    ⟨88277, false, false,
      [11878],
      []⟩,
    ⟨90500, true, false,
      [],
      [7407, 77259]⟩,
    ⟨90522, true, false,
      [],
      [77259]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed084 :
    ∀ move ∈ y322TCIndexRepairRaw084, move.Allowed 48648 226743 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149500. -/
theorem y322TCIndexRepairChecked084 :
    y322TCIndexRepairChecked ⟨149500, by decide⟩ y322TCIndexRepairRaw084
      y322TCIndexRepairAllowed084 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid084
    (hp : ∀ j : Fin 174819, j.val < 149500 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149500, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed084
    y322TCIndexRepairChecked084 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
