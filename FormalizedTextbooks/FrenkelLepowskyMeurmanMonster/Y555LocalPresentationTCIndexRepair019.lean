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

/-- Literal original-source and earlier-equation contexts replacing instruction 149005. -/
def y322TCIndexRepairRaw019 : List Y322RawContextEquationMove :=
  [
    ⟨82641, false, false,
      [],
      []⟩,
    ⟨226247, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed019 :
    ∀ move ∈ y322TCIndexRepairRaw019, move.Allowed 48648 226248 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149005. -/
theorem y322TCIndexRepairChecked019 :
    y322TCIndexRepairChecked ⟨149005, by decide⟩ y322TCIndexRepairRaw019
      y322TCIndexRepairAllowed019 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid019
    (hp : ∀ j : Fin 174819, j.val < 149005 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149005, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed019
    y322TCIndexRepairChecked019 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
