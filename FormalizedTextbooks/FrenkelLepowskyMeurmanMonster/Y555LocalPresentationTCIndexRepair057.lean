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

/-- Literal original-source and earlier-equation contexts replacing instruction 149267. -/
def y322TCIndexRepairRaw057 : List Y322RawContextEquationMove :=
  [
    ⟨93059, false, false,
      [],
      []⟩,
    ⟨93061, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed057 :
    ∀ move ∈ y322TCIndexRepairRaw057, move.Allowed 48648 226510 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149267. -/
theorem y322TCIndexRepairChecked057 :
    y322TCIndexRepairChecked ⟨149267, by decide⟩ y322TCIndexRepairRaw057
      y322TCIndexRepairAllowed057 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid057
    (hp : ∀ j : Fin 174819, j.val < 149267 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149267, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed057
    y322TCIndexRepairChecked057 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
