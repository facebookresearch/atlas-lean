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

/-- Literal original-source and earlier-equation contexts replacing instruction 149697. -/
def y322TCIndexRepairRaw113 : List Y322RawContextEquationMove :=
  [
    ⟨172, false, false,
      [214],
      [77355, 9]⟩,
    ⟨78111, true, false,
      [214, 213],
      [9]⟩,
    ⟨171, false, false,
      [214],
      [77221, 5, 9]⟩,
    ⟨77751, true, false,
      [214, 199],
      [5, 9]⟩,
    ⟨78112, true, false,
      [214],
      [9, 5, 9]⟩,
    ⟨78125, false, false,
      [214, 77355],
      []⟩,
    ⟨78118, false, false,
      [214],
      []⟩,
    ⟨78119, false, false,
      [214],
      []⟩,
    ⟨173, true, false,
      [],
      [77355]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed113 :
    ∀ move ∈ y322TCIndexRepairRaw113, move.Allowed 48648 226940 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149697. -/
theorem y322TCIndexRepairChecked113 :
    y322TCIndexRepairChecked ⟨149697, by decide⟩ y322TCIndexRepairRaw113
      y322TCIndexRepairAllowed113 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid113
    (hp : ∀ j : Fin 174819, j.val < 149697 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149697, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed113
    y322TCIndexRepairChecked113 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
