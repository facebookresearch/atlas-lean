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

/-- Literal original-source and earlier-equation contexts replacing instruction 149440. -/
def y322TCIndexRepairRaw076 : List Y322RawContextEquationMove :=
  [
    ⟨77256, false, false,
      [1752],
      [1753, 77261, 5]⟩,
    ⟨78263, true, false,
      [],
      [5]⟩,
    ⟨77973, true, false,
      [],
      [5]⟩,
    ⟨81822, true, false,
      [1752],
      [15, 5]⟩,
    ⟨81516, true, false,
      [1752],
      [15, 5]⟩,
    ⟨77273, true, false,
      [1752, 78407],
      [5]⟩,
    ⟨77270, true, false,
      [1752, 78407],
      [5]⟩,
    ⟨81820, false, false,
      [1752],
      [5, 5]⟩,
    ⟨77271, false, false,
      [1752, 78545],
      []⟩,
    ⟨81517, true, false,
      [],
      [78545]⟩,
    ⟨3819, false, false,
      [1755, 7508],
      [78545]⟩,
    ⟨3818, true, true,
      [1755, 7508],
      [5857, 78545]⟩,
    ⟨87711, false, false,
      [1755, 7508, 7506],
      [78545]⟩,
    ⟨81818, true, false,
      [1755, 7508, 7506, 5858],
      []⟩,
    ⟨87710, false, false,
      [1755, 7508, 7506, 5858],
      [15]⟩,
    ⟨88318, false, false,
      [1755, 7508, 7506],
      [15]⟩,
    ⟨77587, false, false,
      [1755, 7508],
      []⟩,
    ⟨3820, true, false,
      [1755],
      [77185]⟩,
    ⟨89230, false, false,
      [1755, 7511],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed076 :
    ∀ move ∈ y322TCIndexRepairRaw076, move.Allowed 48648 226683 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149440. -/
theorem y322TCIndexRepairChecked076 :
    y322TCIndexRepairChecked ⟨149440, by decide⟩ y322TCIndexRepairRaw076
      y322TCIndexRepairAllowed076 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid076
    (hp : ∀ j : Fin 174819, j.val < 149440 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149440, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed076
    y322TCIndexRepairChecked076 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
