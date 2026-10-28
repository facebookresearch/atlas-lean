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

/-- Literal original-source and earlier-equation contexts replacing instruction 149096. -/
def y322TCIndexRepairRaw031 : List Y322RawContextEquationMove :=
  [
    ⟨4501, false, false,
      [3155, 8872],
      [80617]⟩,
    ⟨4500, false, false,
      [3155, 8872],
      [3155, 80617]⟩,
    ⟨88215, false, false,
      [3155, 8872, 8864],
      [80617]⟩,
    ⟨84265, false, false,
      [3155, 8872, 8864],
      [80617]⟩,
    ⟨85342, true, false,
      [3155, 8872, 8864],
      []⟩,
    ⟨85429, true, false,
      [3155, 8872, 8864],
      [5]⟩,
    ⟨77405, true, false,
      [3155, 8872, 8864, 77165],
      []⟩,
    ⟨77404, true, false,
      [3155, 8872, 8864, 77165],
      []⟩,
    ⟨85441, false, false,
      [3155, 8872, 8864],
      [1]⟩,
    ⟨85438, true, false,
      [3155, 8872, 8864],
      [1]⟩,
    ⟨89015, true, false,
      [3155, 8872, 8864, 8860],
      [5, 1]⟩,
    ⟨85670, false, false,
      [3155, 8872, 8864, 8860],
      [1]⟩,
    ⟨89007, false, false,
      [3155, 8872, 8864, 8860],
      [1]⟩,
    ⟨89013, false, true,
      [3155, 8872, 8864],
      [8847, 77451, 1]⟩,
    ⟨89016, true, false,
      [3155, 8872, 8864],
      [77451, 1]⟩,
    ⟨78628, false, false,
      [3155, 8872],
      []⟩,
    ⟨4502, true, false,
      [3155],
      [77453]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed031 :
    ∀ move ∈ y322TCIndexRepairRaw031, move.Allowed 48648 226339 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149096. -/
theorem y322TCIndexRepairChecked031 :
    y322TCIndexRepairChecked ⟨149096, by decide⟩ y322TCIndexRepairRaw031
      y322TCIndexRepairAllowed031 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid031
    (hp : ∀ j : Fin 174819, j.val < 149096 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149096, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed031
    y322TCIndexRepairChecked031 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
