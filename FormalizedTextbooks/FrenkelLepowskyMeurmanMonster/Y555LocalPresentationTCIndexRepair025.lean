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

/-- Literal original-source and earlier-equation contexts replacing instruction 149048. -/
def y322TCIndexRepairRaw025 : List Y322RawContextEquationMove :=
  [
    ⟨83632, true, false,
      [3152],
      [3]⟩,
    ⟨77263, false, false,
      [3152, 79211],
      []⟩,
    ⟨83619, true, false,
      [],
      [79211]⟩,
    ⟨89315, false, false,
      [3155],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed025 :
    ∀ move ∈ y322TCIndexRepairRaw025, move.Allowed 48648 226291 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149048. -/
theorem y322TCIndexRepairChecked025 :
    y322TCIndexRepairChecked ⟨149048, by decide⟩ y322TCIndexRepairRaw025
      y322TCIndexRepairAllowed025 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid025
    (hp : ∀ j : Fin 174819, j.val < 149048 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149048, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed025
    y322TCIndexRepairChecked025 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
