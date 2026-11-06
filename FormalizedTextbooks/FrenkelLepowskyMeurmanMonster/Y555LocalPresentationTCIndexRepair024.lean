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

/-- Literal original-source and earlier-equation contexts replacing instruction 149040. -/
def y322TCIndexRepairRaw024 : List Y322RawContextEquationMove :=
  [
    ⟨82908, true, false,
      [],
      [5]⟩,
    ⟨77271, false, false,
      [79035],
      []⟩,
    ⟨82900, false, false,
      [],
      []⟩,
    ⟨84291, true, false,
      [],
      []⟩,
    ⟨89263, true, false,
      [9194],
      [7]⟩,
    ⟨85145, true, false,
      [9194],
      [7]⟩,
    ⟨77280, false, false,
      [9194, 80245],
      []⟩,
    ⟨77283, false, false,
      [9194, 80245],
      []⟩,
    ⟨85117, false, false,
      [9194],
      [15]⟩,
    ⟨85149, false, false,
      [9194],
      []⟩,
    ⟨84369, false, false,
      [9194],
      []⟩,
    ⟨84370, false, false,
      [9194],
      []⟩,
    ⟨84370, false, false,
      [9194],
      []⟩,
    ⟨85150, false, false,
      [9194],
      []⟩,
    ⟨85151, false, false,
      [9194],
      []⟩,
    ⟨88084, false, false,
      [9194],
      []⟩,
    ⟨89257, true, false,
      [],
      [7055, 77617]⟩,
    ⟨89269, true, false,
      [],
      [77617]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed024 :
    ∀ move ∈ y322TCIndexRepairRaw024, move.Allowed 48648 226283 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149040. -/
theorem y322TCIndexRepairChecked024 :
    y322TCIndexRepairChecked ⟨149040, by decide⟩ y322TCIndexRepairRaw024
      y322TCIndexRepairAllowed024 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid024
    (hp : ∀ j : Fin 174819, j.val < 149040 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149040, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed024
    y322TCIndexRepairChecked024 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
