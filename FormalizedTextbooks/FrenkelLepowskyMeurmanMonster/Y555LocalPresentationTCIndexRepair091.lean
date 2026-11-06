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

/-- Literal original-source and earlier-equation contexts replacing instruction 149546. -/
def y322TCIndexRepairRaw091 : List Y322RawContextEquationMove :=
  [
    ⟨77289, true, false,
      [77305],
      []⟩,
    ⟨38718, true, false,
      [],
      [9]⟩,
    ⟨88589, true, false,
      [8138],
      [9]⟩,
    ⟨2660, false, false,
      [8138, 5190],
      [78433, 9]⟩,
    ⟨87446, false, false,
      [8138, 5190],
      [5187, 78433, 9]⟩,
    ⟨39281, false, false,
      [8138, 5190, 5184, 5187],
      [9]⟩,
    ⟨2658, false, false,
      [8138, 5190, 5184],
      [78431, 11, 9]⟩,
    ⟨82477, true, false,
      [8138, 5190, 5184, 275],
      [11, 9]⟩,
    ⟨81277, true, false,
      [8138, 5190, 5184],
      [9, 11, 9]⟩,
    ⟨81278, true, false,
      [8138, 5190, 5184],
      [9, 11, 9]⟩,
    ⟨79588, true, false,
      [8138, 5190, 5184, 78283],
      [9]⟩,
    ⟨87445, true, false,
      [8138, 5190, 5184, 78283],
      [9]⟩,
    ⟨87440, false, false,
      [8138, 5190, 5184],
      [11, 9, 9]⟩,
    ⟨87411, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 9, 9]⟩,
    ⟨87203, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 9, 9]⟩,
    ⟨87203, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 9, 9]⟩,
    ⟨41217, false, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 9, 9]⟩,
    ⟨77353, false, false,
      [8138, 5190, 5184, 5167, 5106, 77185],
      [9, 9]⟩,
    ⟨77354, false, false,
      [8138, 5190, 5184, 5167, 5106, 77185],
      [9, 9]⟩,
    ⟨77915, false, false,
      [8138, 5190, 5184, 5167, 5106],
      [77185, 11, 1, 9, 9]⟩,
    ⟨77586, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 1, 9, 9]⟩,
    ⟨77586, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 1, 9, 9]⟩,
    ⟨77651, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 1, 9, 9]⟩,
    ⟨85924, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 1, 9, 9]⟩,
    ⟨77915, false, false,
      [8138, 5190, 5184, 5167, 5106],
      [77183, 13, 11, 1, 9, 9]⟩,
    ⟨77581, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [13, 11, 1, 9, 9]⟩,
    ⟨77582, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [1, 13, 11, 1, 9, 9]⟩,
    ⟨77582, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [1, 13, 11, 1, 9, 9]⟩,
    ⟨77652, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [1, 13, 11, 1, 9, 9]⟩,
    ⟨85909, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [1, 13, 11, 1, 9, 9]⟩,
    ⟨77354, true, false,
      [8138, 5190, 5184, 5167, 5106, 77179],
      [13, 11, 1, 9, 9]⟩,
    ⟨77353, true, false,
      [8138, 5190, 5184, 5167, 5106, 77179],
      [13, 11, 1, 9, 9]⟩,
    ⟨86586, false, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 13, 11, 1, 9, 9]⟩,
    ⟨77326, true, false,
      [8138, 5190, 5184, 5167, 5106, 81767],
      [11, 1, 9, 9]⟩,
    ⟨77325, true, false,
      [8138, 5190, 5184, 5167, 5106, 81767],
      [11, 1, 9, 9]⟩,
    ⟨41125, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [11, 11, 1, 9, 9]⟩,
    ⟨77296, false, false,
      [8138, 5190, 5184, 5167, 5106, 82121],
      [1, 9, 9]⟩,
    ⟨41126, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [9, 9]⟩,
    ⟨77915, true, false,
      [8138, 5190, 5184, 5167, 5106],
      [82123, 9, 9]⟩,
    ⟨2618, false, true,
      [8138, 5190, 5184, 5167],
      [82123, 9, 9]⟩,
    ⟨2657, true, false,
      [8138, 5190, 5184],
      [82123, 9, 9]⟩,
    ⟨77289, false, false,
      [8138, 5190, 82123],
      []⟩,
    ⟨2661, true, false,
      [8138],
      [82123]⟩,
    ⟨88332, false, false,
      [8138, 5193],
      []⟩,
    ⟨88427, false, false,
      [8138, 5193, 7563],
      []⟩,
    ⟨4091, true, false,
      [8138, 5193],
      [77143]⟩,
    ⟨4138, true, false,
      [8138],
      [77143]⟩,
    ⟨4135, true, false,
      [],
      [8147, 77143]⟩,
    ⟨4139, true, false,
      [],
      [77143]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed091 :
    ∀ move ∈ y322TCIndexRepairRaw091, move.Allowed 48648 226789 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149546. -/
theorem y322TCIndexRepairChecked091 :
    y322TCIndexRepairChecked ⟨149546, by decide⟩ y322TCIndexRepairRaw091
      y322TCIndexRepairAllowed091 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid091
    (hp : ∀ j : Fin 174819, j.val < 149546 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149546, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed091
    y322TCIndexRepairChecked091 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
