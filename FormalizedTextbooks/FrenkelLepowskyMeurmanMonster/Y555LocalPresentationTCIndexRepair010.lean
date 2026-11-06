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

/-- Literal original-source and earlier-equation contexts replacing instruction 148921. -/
def y322TCIndexRepairRaw010 : List Y322RawContextEquationMove :=
  [
    ⟨77514, false, false,
      [],
      []⟩,
    ⟨77681, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed010 :
    ∀ move ∈ y322TCIndexRepairRaw010, move.Allowed 48648 226164 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148921. -/
theorem y322TCIndexRepairChecked010 :
    y322TCIndexRepairChecked ⟨148921, by decide⟩ y322TCIndexRepairRaw010
      y322TCIndexRepairAllowed010 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid010
    (hp : ∀ j : Fin 174819, j.val < 148921 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148921, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed010
    y322TCIndexRepairChecked010 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
