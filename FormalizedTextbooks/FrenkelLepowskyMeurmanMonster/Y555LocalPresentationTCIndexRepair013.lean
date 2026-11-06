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

/-- Literal original-source and earlier-equation contexts replacing instruction 148951. -/
def y322TCIndexRepairRaw013 : List Y322RawContextEquationMove :=
  [
    ⟨3819, false, false,
      [7508],
      [78545]⟩,
    ⟨3818, true, true,
      [7508],
      [5857, 78545]⟩,
    ⟨87711, false, false,
      [7508, 7506],
      [78545]⟩,
    ⟨81818, true, false,
      [7508, 7506, 5858],
      []⟩,
    ⟨87710, false, false,
      [7508, 7506, 5858],
      [15]⟩,
    ⟨88318, false, false,
      [7508, 7506],
      [15]⟩,
    ⟨77587, false, false,
      [7508],
      []⟩,
    ⟨3820, true, false,
      [],
      [77185]⟩,
    ⟨89230, false, false,
      [7511],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed013 :
    ∀ move ∈ y322TCIndexRepairRaw013, move.Allowed 48648 226194 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148951. -/
theorem y322TCIndexRepairChecked013 :
    y322TCIndexRepairChecked ⟨148951, by decide⟩ y322TCIndexRepairRaw013
      y322TCIndexRepairAllowed013 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid013
    (hp : ∀ j : Fin 174819, j.val < 148951 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148951, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed013
    y322TCIndexRepairChecked013 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
