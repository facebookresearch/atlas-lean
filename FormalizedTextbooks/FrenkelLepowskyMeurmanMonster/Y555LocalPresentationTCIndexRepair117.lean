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

/-- Literal original-source and earlier-equation contexts replacing instruction 149736. -/
def y322TCIndexRepairRaw117 : List Y322RawContextEquationMove :=
  [
    ⟨79622, false, false,
      [292],
      [77365, 7]⟩,
    ⟨78466, true, false,
      [],
      [7]⟩,
    ⟨80692, true, false,
      [292],
      [7]⟩,
    ⟨80691, true, false,
      [292],
      [7]⟩,
    ⟨78463, true, false,
      [],
      [7]⟩,
    ⟨78382, true, false,
      [292],
      [13, 7]⟩,
    ⟨78382, true, false,
      [292],
      [13, 7]⟩,
    ⟨78381, true, false,
      [292],
      [13, 7]⟩,
    ⟨93370, true, false,
      [292],
      [13, 7]⟩,
    ⟨93369, true, false,
      [292],
      [13, 7]⟩,
    ⟨77317, true, false,
      [292, 82747],
      [7]⟩,
    ⟨77316, true, false,
      [292, 82747],
      [7]⟩,
    ⟨93442, false, false,
      [292],
      [7, 7]⟩,
    ⟨77281, false, false,
      [292, 82753],
      []⟩,
    ⟨78364, true, false,
      [],
      [82753]⟩,
    ⟨93549, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed117 :
    ∀ move ∈ y322TCIndexRepairRaw117, move.Allowed 48648 226979 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149736. -/
theorem y322TCIndexRepairChecked117 :
    y322TCIndexRepairChecked ⟨149736, by decide⟩ y322TCIndexRepairRaw117
      y322TCIndexRepairAllowed117 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid117
    (hp : ∀ j : Fin 174819, j.val < 149736 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149736, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed117
    y322TCIndexRepairChecked117 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
