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

/-- Literal original-source and earlier-equation contexts replacing instruction 149746. -/
def y322TCIndexRepairRaw118 : List Y322RawContextEquationMove :=
  [
    ⟨78494, false, false,
      [],
      []⟩,
    ⟨78485, true, false,
      [],
      [11]⟩,
    ⟨77387, false, false,
      [77365],
      []⟩,
    ⟨77388, false, false,
      [77365],
      []⟩,
    ⟨78475, false, false,
      [],
      [3]⟩,
    ⟨78476, false, false,
      [],
      [3]⟩,
    ⟨78473, false, false,
      [],
      [3]⟩,
    ⟨78474, false, false,
      [],
      [3]⟩,
    ⟨78474, false, false,
      [],
      [3]⟩,
    ⟨78482, false, false,
      [245],
      []⟩,
    ⟨78492, false, false,
      [],
      []⟩,
    ⟨78493, false, false,
      [],
      []⟩,
    ⟨78490, false, false,
      [245],
      []⟩,
    ⟨78166, true, false,
      [],
      [77367]⟩,
    ⟨78492, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed118 :
    ∀ move ∈ y322TCIndexRepairRaw118, move.Allowed 48648 226989 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149746. -/
theorem y322TCIndexRepairChecked118 :
    y322TCIndexRepairChecked ⟨149746, by decide⟩ y322TCIndexRepairRaw118
      y322TCIndexRepairAllowed118 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid118
    (hp : ∀ j : Fin 174819, j.val < 149746 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149746, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed118
    y322TCIndexRepairChecked118 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
