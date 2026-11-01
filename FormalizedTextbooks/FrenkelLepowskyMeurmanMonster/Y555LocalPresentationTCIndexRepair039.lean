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

/-- Literal original-source and earlier-equation contexts replacing instruction 149153. -/
def y322TCIndexRepairRaw039 : List Y322RawContextEquationMove :=
  [
    ⟨89093, true, false,
      [8976],
      []⟩,
    ⟨89087, true, false,
      [],
      [77149]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed039 :
    ∀ move ∈ y322TCIndexRepairRaw039, move.Allowed 48648 226396 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149153. -/
theorem y322TCIndexRepairChecked039 :
    y322TCIndexRepairChecked ⟨149153, by decide⟩ y322TCIndexRepairRaw039
      y322TCIndexRepairAllowed039 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid039
    (hp : ∀ j : Fin 174819, j.val < 149153 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149153, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed039
    y322TCIndexRepairChecked039 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
