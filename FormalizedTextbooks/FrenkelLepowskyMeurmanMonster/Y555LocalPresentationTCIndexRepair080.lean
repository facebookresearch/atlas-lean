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

/-- Literal original-source and earlier-equation contexts replacing instruction 149471. -/
def y322TCIndexRepairRaw080 : List Y322RawContextEquationMove :=
  [
    ⟨39568, true, false,
      [],
      []⟩,
    ⟨82766, true, false,
      [1752],
      []⟩,
    ⟨83298, true, false,
      [1752, 2926],
      [3]⟩,
    ⟨77263, false, false,
      [1752, 2926, 77629],
      []⟩,
    ⟨1529, true, false,
      [1752],
      [77629]⟩,
    ⟨81517, true, false,
      [],
      [2929, 77629]⟩,
    ⟨1530, true, false,
      [],
      [77629]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed080 :
    ∀ move ∈ y322TCIndexRepairRaw080, move.Allowed 48648 226714 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149471. -/
theorem y322TCIndexRepairChecked080 :
    y322TCIndexRepairChecked ⟨149471, by decide⟩ y322TCIndexRepairRaw080
      y322TCIndexRepairAllowed080 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid080
    (hp : ∀ j : Fin 174819, j.val < 149471 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149471, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed080
    y322TCIndexRepairChecked080 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
