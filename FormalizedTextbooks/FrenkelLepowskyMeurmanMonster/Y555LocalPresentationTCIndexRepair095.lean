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

/-- Literal original-source and earlier-equation contexts replacing instruction 149589. -/
def y322TCIndexRepairRaw095 : List Y322RawContextEquationMove :=
  [
    ⟨78038, true, false,
      [],
      [13]⟩,
    ⟨77256, false, false,
      [1764],
      [1765, 77319, 3, 13]⟩,
    ⟨81539, true, false,
      [],
      [3, 13]⟩,
    ⟨78040, true, false,
      [],
      [3, 13]⟩,
    ⟨81532, true, false,
      [1764],
      [5, 3, 13]⟩,
    ⟨77423, true, false,
      [1764, 77321],
      [3, 13]⟩,
    ⟨77422, true, false,
      [1764, 77321],
      [3, 13]⟩,
    ⟨81534, false, false,
      [1764],
      [13, 3, 13]⟩,
    ⟨78375, false, false,
      [1764, 77319],
      []⟩,
    ⟨77264, false, false,
      [1764, 77319],
      []⟩,
    ⟨81542, false, false,
      [1764],
      []⟩,
    ⟨81545, false, false,
      [1764],
      []⟩,
    ⟨952, true, false,
      [],
      [77317]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed095 :
    ∀ move ∈ y322TCIndexRepairRaw095, move.Allowed 48648 226832 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149589. -/
theorem y322TCIndexRepairChecked095 :
    y322TCIndexRepairChecked ⟨149589, by decide⟩ y322TCIndexRepairRaw095
      y322TCIndexRepairAllowed095 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid095
    (hp : ∀ j : Fin 174819, j.val < 149589 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149589, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed095
    y322TCIndexRepairChecked095 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
