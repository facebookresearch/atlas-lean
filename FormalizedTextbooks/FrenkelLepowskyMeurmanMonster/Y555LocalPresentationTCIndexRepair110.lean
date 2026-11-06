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

/-- Literal original-source and earlier-equation contexts replacing instruction 149670. -/
def y322TCIndexRepairRaw110 : List Y322RawContextEquationMove :=
  [
    ⟨78062, true, false,
      [],
      [3]⟩,
    ⟨308, false, false,
      [486],
      [77347, 1, 3]⟩,
    ⟨78792, true, false,
      [486, 479],
      [1, 3]⟩,
    ⟨78788, true, false,
      [486],
      [3, 1, 3]⟩,
    ⟨78790, true, false,
      [486],
      [3, 1, 3]⟩,
    ⟨77727, false, false,
      [486, 77481],
      []⟩,
    ⟨77728, false, false,
      [486, 77481],
      []⟩,
    ⟨78792, false, false,
      [486],
      [1]⟩,
    ⟨78791, false, false,
      [486],
      [1]⟩,
    ⟨78062, false, false,
      [486, 253],
      []⟩,
    ⟨309, true, false,
      [],
      [253, 77345]⟩,
    ⟨310, true, false,
      [],
      [77345]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed110 :
    ∀ move ∈ y322TCIndexRepairRaw110, move.Allowed 48648 226913 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149670. -/
theorem y322TCIndexRepairChecked110 :
    y322TCIndexRepairChecked ⟨149670, by decide⟩ y322TCIndexRepairRaw110
      y322TCIndexRepairAllowed110 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid110
    (hp : ∀ j : Fin 174819, j.val < 149670 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149670, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed110
    y322TCIndexRepairChecked110 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
