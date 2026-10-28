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

/-- Literal original-source and earlier-equation contexts replacing instruction 149635. -/
def y322TCIndexRepairRaw105 : List Y322RawContextEquationMove :=
  [
    ⟨38732, true, false,
      [],
      []⟩,
    ⟨78050, true, false,
      [],
      []⟩,
    ⟨78050, true, false,
      [],
      []⟩,
    ⟨78078, true, false,
      [],
      []⟩,
    ⟨78809, true, false,
      [],
      []⟩,
    ⟨78807, true, false,
      [498],
      [3]⟩,
    ⟨77263, false, false,
      [498, 77333],
      []⟩,
    ⟨78808, true, false,
      [],
      [77333]⟩,
    ⟨78812, true, false,
      [],
      [77333]⟩,
    ⟨78811, true, false,
      [],
      [77333]⟩,
    ⟨78810, true, false,
      [],
      [77333]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed105 :
    ∀ move ∈ y322TCIndexRepairRaw105, move.Allowed 48648 226878 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149635. -/
theorem y322TCIndexRepairChecked105 :
    y322TCIndexRepairChecked ⟨149635, by decide⟩ y322TCIndexRepairRaw105
      y322TCIndexRepairAllowed105 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid105
    (hp : ∀ j : Fin 174819, j.val < 149635 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149635, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed105
    y322TCIndexRepairChecked105 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
