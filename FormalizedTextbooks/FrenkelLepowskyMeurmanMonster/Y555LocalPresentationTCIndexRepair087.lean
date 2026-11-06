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

/-- Literal original-source and earlier-equation contexts replacing instruction 149518. -/
def y322TCIndexRepairRaw087 : List Y322RawContextEquationMove :=
  [
    ⟨78008, true, false,
      [],
      [1]⟩,
    ⟨77251, false, false,
      [77291],
      []⟩,
    ⟨78009, false, false,
      [],
      []⟩,
    ⟨78089, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed087 :
    ∀ move ∈ y322TCIndexRepairRaw087, move.Allowed 48648 226761 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149518. -/
theorem y322TCIndexRepairChecked087 :
    y322TCIndexRepairChecked ⟨149518, by decide⟩ y322TCIndexRepairRaw087
      y322TCIndexRepairAllowed087 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid087
    (hp : ∀ j : Fin 174819, j.val < 149518 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149518, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed087
    y322TCIndexRepairChecked087 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
