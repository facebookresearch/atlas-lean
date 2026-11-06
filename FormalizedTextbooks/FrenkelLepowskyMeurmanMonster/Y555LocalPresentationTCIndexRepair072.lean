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

/-- Literal original-source and earlier-equation contexts replacing instruction 149397. -/
def y322TCIndexRepairRaw072 : List Y322RawContextEquationMove :=
  [
    ⟨79691, true, false,
      [292],
      [3]⟩,
    ⟨77263, false, false,
      [292, 77725],
      []⟩,
    ⟨78364, true, false,
      [],
      [77725]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed072 :
    ∀ move ∈ y322TCIndexRepairRaw072, move.Allowed 48648 226640 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149397. -/
theorem y322TCIndexRepairChecked072 :
    y322TCIndexRepairChecked ⟨149397, by decide⟩ y322TCIndexRepairRaw072
      y322TCIndexRepairAllowed072 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid072
    (hp : ∀ j : Fin 174819, j.val < 149397 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149397, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed072
    y322TCIndexRepairChecked072 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
