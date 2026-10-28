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

/-- Literal original-source and earlier-equation contexts replacing instruction 149012. -/
def y322TCIndexRepairRaw020 : List Y322RawContextEquationMove :=
  [
    ⟨82877, true, false,
      [],
      []⟩,
    ⟨88375, true, false,
      [7660],
      [9]⟩,
    ⟨84938, false, false,
      [7660],
      []⟩,
    ⟨88374, false, true,
      [],
      [4197, 77563]⟩,
    ⟨88377, true, false,
      [],
      [77563]⟩,
    ⟨88399, false, false,
      [7667],
      []⟩,
    ⟨88413, false, false,
      [7667, 7693],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed020 :
    ∀ move ∈ y322TCIndexRepairRaw020, move.Allowed 48648 226255 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149012. -/
theorem y322TCIndexRepairChecked020 :
    y322TCIndexRepairChecked ⟨149012, by decide⟩ y322TCIndexRepairRaw020
      y322TCIndexRepairAllowed020 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid020
    (hp : ∀ j : Fin 174819, j.val < 149012 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149012, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed020
    y322TCIndexRepairChecked020 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
