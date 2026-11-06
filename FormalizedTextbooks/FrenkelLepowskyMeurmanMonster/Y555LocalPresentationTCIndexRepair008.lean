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

/-- Literal original-source and earlier-equation contexts replacing instruction 148905. -/
def y322TCIndexRepairRaw008 : List Y322RawContextEquationMove :=
  [
    ⟨77509, true, false,
      [],
      [13]⟩,
    ⟨77509, true, false,
      [],
      [13]⟩,
    ⟨77508, true, false,
      [],
      [13]⟩,
    ⟨77507, true, false,
      [],
      [13]⟩,
    ⟨77390, false, false,
      [77117],
      []⟩,
    ⟨77391, false, false,
      [77117],
      []⟩,
    ⟨77506, false, false,
      [],
      [3]⟩,
    ⟨77500, false, false,
      [],
      [3]⟩,
    ⟨77507, false, false,
      [13],
      []⟩,
    ⟨77335, true, false,
      [],
      [77119]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed008 :
    ∀ move ∈ y322TCIndexRepairRaw008, move.Allowed 48648 226148 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148905. -/
theorem y322TCIndexRepairChecked008 :
    y322TCIndexRepairChecked ⟨148905, by decide⟩ y322TCIndexRepairRaw008
      y322TCIndexRepairAllowed008 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid008
    (hp : ∀ j : Fin 174819, j.val < 148905 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148905, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed008
    y322TCIndexRepairChecked008 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
