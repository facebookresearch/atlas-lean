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

/-- Literal original-source and earlier-equation contexts replacing instruction 148893. -/
def y322TCIndexRepairRaw007 : List Y322RawContextEquationMove :=
  [
    ⟨80085, true, false,
      [],
      [7]⟩,
    ⟨77281, false, false,
      [77859],
      []⟩,
    ⟨80074, false, false,
      [],
      []⟩,
    ⟨80073, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed007 :
    ∀ move ∈ y322TCIndexRepairRaw007, move.Allowed 48648 226136 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148893. -/
theorem y322TCIndexRepairChecked007 :
    y322TCIndexRepairChecked ⟨148893, by decide⟩ y322TCIndexRepairRaw007
      y322TCIndexRepairAllowed007 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid007
    (hp : ∀ j : Fin 174819, j.val < 148893 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148893, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed007
    y322TCIndexRepairChecked007 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
