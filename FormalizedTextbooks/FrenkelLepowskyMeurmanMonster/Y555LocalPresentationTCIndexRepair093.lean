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

/-- Literal original-source and earlier-equation contexts replacing instruction 149566. -/
def y322TCIndexRepairRaw093 : List Y322RawContextEquationMove :=
  [
    ⟨89169, false, false,
      [8129, 9088],
      [79177]⟩,
    ⟨88584, true, false,
      [8129, 9088, 9087],
      []⟩,
    ⟨89166, true, false,
      [8129, 9088],
      [5]⟩,
    ⟨82408, false, false,
      [8129, 9088],
      []⟩,
    ⟨89170, false, false,
      [8129, 9088],
      []⟩,
    ⟨89171, true, false,
      [8129, 9088],
      [77379]⟩,
    ⟨89172, true, false,
      [8129],
      [9093, 77379]⟩,
    ⟨89173, true, false,
      [8129],
      [77379]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed093 :
    ∀ move ∈ y322TCIndexRepairRaw093, move.Allowed 48648 226809 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149566. -/
theorem y322TCIndexRepairChecked093 :
    y322TCIndexRepairChecked ⟨149566, by decide⟩ y322TCIndexRepairRaw093
      y322TCIndexRepairAllowed093 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid093
    (hp : ∀ j : Fin 174819, j.val < 149566 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149566, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed093
    y322TCIndexRepairChecked093 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
