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

/-- Literal original-source and earlier-equation contexts replacing instruction 149493. -/
def y322TCIndexRepairRaw083 : List Y322RawContextEquationMove :=
  [
    ⟨90457, false, false,
      [2405, 11828],
      [78439]⟩,
    ⟨90456, false, false,
      [2405, 11828],
      [8137, 78439]⟩,
    ⟨88586, false, false,
      [2405, 11828, 11824],
      [78439]⟩,
    ⟨88587, false, false,
      [2405, 11828, 11824],
      [78439]⟩,
    ⟨88587, false, false,
      [2405, 11828, 11824],
      [78439]⟩,
    ⟨81684, true, false,
      [2405, 11828, 11824, 8134],
      []⟩,
    ⟨81658, true, false,
      [2405, 11828, 11824, 8134],
      []⟩,
    ⟨88585, false, false,
      [2405, 11828, 11824, 8134],
      [15]⟩,
    ⟨90454, false, false,
      [2405, 11828, 11824],
      []⟩,
    ⟨90455, true, false,
      [2405, 11828, 11824],
      [77195]⟩,
    ⟨90458, true, false,
      [2405],
      [77195]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed083 :
    ∀ move ∈ y322TCIndexRepairRaw083, move.Allowed 48648 226736 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149493. -/
theorem y322TCIndexRepairChecked083 :
    y322TCIndexRepairChecked ⟨149493, by decide⟩ y322TCIndexRepairRaw083
      y322TCIndexRepairAllowed083 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid083
    (hp : ∀ j : Fin 174819, j.val < 149493 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149493, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed083
    y322TCIndexRepairChecked083 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
