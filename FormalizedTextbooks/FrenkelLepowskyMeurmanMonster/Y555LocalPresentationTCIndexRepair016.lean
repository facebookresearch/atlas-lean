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

/-- Literal original-source and earlier-equation contexts replacing instruction 148978. -/
def y322TCIndexRepairRaw016 : List Y322RawContextEquationMove :=
  [
    ⟨81731, true, false,
      [1856],
      [11]⟩,
    ⟨77296, false, false,
      [1856, 78531],
      []⟩,
    ⟨994, true, false,
      [],
      [78531]⟩,
    ⟨87751, false, false,
      [1859],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed016 :
    ∀ move ∈ y322TCIndexRepairRaw016, move.Allowed 48648 226221 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148978. -/
theorem y322TCIndexRepairChecked016 :
    y322TCIndexRepairChecked ⟨148978, by decide⟩ y322TCIndexRepairRaw016
      y322TCIndexRepairAllowed016 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid016
    (hp : ∀ j : Fin 174819, j.val < 148978 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148978, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed016
    y322TCIndexRepairChecked016 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
