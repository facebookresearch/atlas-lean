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

/-- Literal original-source and earlier-equation contexts replacing instruction 149628. -/
def y322TCIndexRepairRaw104 : List Y322RawContextEquationMove :=
  [
    ⟨704, false, false,
      [1278],
      [77331, 3]⟩,
    ⟨79237, true, false,
      [1278, 547],
      [3]⟩,
    ⟨338, false, false,
      [1278],
      [77203, 9, 3]⟩,
    ⟨78943, true, false,
      [1278, 315],
      [9, 3]⟩,
    ⟨78947, true, false,
      [1278],
      [3, 9, 3]⟩,
    ⟨78947, true, false,
      [1278],
      [3, 9, 3]⟩,
    ⟨78946, true, false,
      [1278],
      [3, 9, 3]⟩,
    ⟨80468, true, false,
      [1278],
      [3, 9, 3]⟩,
    ⟨78682, false, false,
      [1278, 77993],
      []⟩,
    ⟨80476, true, false,
      [],
      [77993]⟩,
    ⟨89945, false, false,
      [1281],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed104 :
    ∀ move ∈ y322TCIndexRepairRaw104, move.Allowed 48648 226871 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149628. -/
theorem y322TCIndexRepairChecked104 :
    y322TCIndexRepairChecked ⟨149628, by decide⟩ y322TCIndexRepairRaw104
      y322TCIndexRepairAllowed104 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid104
    (hp : ∀ j : Fin 174819, j.val < 149628 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149628, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed104
    y322TCIndexRepairChecked104 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
