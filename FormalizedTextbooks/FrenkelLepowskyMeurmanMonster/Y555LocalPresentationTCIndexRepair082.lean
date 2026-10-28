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

/-- Literal original-source and earlier-equation contexts replacing instruction 149486. -/
def y322TCIndexRepairRaw082 : List Y322RawContextEquationMove :=
  [
    ⟨88333, false, false,
      [1491, 7564],
      [78289]⟩,
    ⟨88331, true, true,
      [1491, 7564],
      [5189, 78289]⟩,
    ⟨87996, false, false,
      [1491, 7564, 7562],
      [78289]⟩,
    ⟨87446, false, false,
      [1491, 7564, 7562],
      [78289]⟩,
    ⟨77271, true, false,
      [1491, 7564, 7562, 5184, 78289],
      []⟩,
    ⟨87484, false, false,
      [1491, 7564, 7562, 5184],
      [5]⟩,
    ⟨88332, false, false,
      [1491, 7564, 7562],
      [5]⟩,
    ⟨78582, false, false,
      [1491, 7564],
      []⟩,
    ⟨88334, true, false,
      [1491],
      [77385]⟩,
    ⟨90565, false, false,
      [1491, 7567],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed082 :
    ∀ move ∈ y322TCIndexRepairRaw082, move.Allowed 48648 226729 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149486. -/
theorem y322TCIndexRepairChecked082 :
    y322TCIndexRepairChecked ⟨149486, by decide⟩ y322TCIndexRepairRaw082
      y322TCIndexRepairAllowed082 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid082
    (hp : ∀ j : Fin 174819, j.val < 149486 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149486, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed082
    y322TCIndexRepairChecked082 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
