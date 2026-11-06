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

/-- Literal original-source and earlier-equation contexts replacing instruction 149251. -/
def y322TCIndexRepairRaw055 : List Y322RawContextEquationMove :=
  [
    ⟨77608, true, false,
      [],
      [11]⟩,
    ⟨77857, true, false,
      [150],
      [15, 11]⟩,
    ⟨77858, false, false,
      [150, 77205],
      []⟩,
    ⟨77253, false, false,
      [150, 77205],
      []⟩,
    ⟨77608, false, false,
      [150],
      []⟩,
    ⟨77643, false, false,
      [150],
      []⟩,
    ⟨77607, false, false,
      [150],
      []⟩,
    ⟨77607, false, false,
      [150],
      []⟩,
    ⟨77859, false, false,
      [150],
      []⟩,
    ⟨77813, true, false,
      [],
      [77203]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed055 :
    ∀ move ∈ y322TCIndexRepairRaw055, move.Allowed 48648 226494 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149251. -/
theorem y322TCIndexRepairChecked055 :
    y322TCIndexRepairChecked ⟨149251, by decide⟩ y322TCIndexRepairRaw055
      y322TCIndexRepairAllowed055 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid055
    (hp : ∀ j : Fin 174819, j.val < 149251 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149251, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed055
    y322TCIndexRepairChecked055 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
