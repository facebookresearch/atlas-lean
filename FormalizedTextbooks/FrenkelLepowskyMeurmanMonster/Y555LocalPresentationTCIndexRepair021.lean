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

/-- Literal original-source and earlier-equation contexts replacing instruction 149024. -/
def y322TCIndexRepairRaw021 : List Y322RawContextEquationMove :=
  [
    ⟨88384, false, false,
      [7674],
      [79203]⟩,
    ⟨83607, true, false,
      [7674, 7672],
      []⟩,
    ⟨83608, true, false,
      [7674, 7672],
      []⟩,
    ⟨77296, true, false,
      [7674, 7672, 79203],
      []⟩,
    ⟨83609, false, false,
      [7674, 7672],
      [11]⟩,
    ⟨88378, false, false,
      [7674, 7672],
      [11]⟩,
    ⟨84935, true, false,
      [7674, 7672, 7667, 4182],
      [11]⟩,
    ⟨84933, false, false,
      [7674, 7672, 7667, 4182],
      []⟩,
    ⟨84934, false, false,
      [7674, 7672, 7667, 4182],
      []⟩,
    ⟨84936, true, false,
      [7674, 7672, 7667],
      [80243]⟩,
    ⟨88034, false, false,
      [7674, 7672, 7667, 4181],
      []⟩,
    ⟨88381, true, false,
      [7674, 7672, 7667],
      [77443]⟩,
    ⟨88382, true, false,
      [7674, 7672],
      [77443]⟩,
    ⟨88385, true, false,
      [],
      [77443]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed021 :
    ∀ move ∈ y322TCIndexRepairRaw021, move.Allowed 48648 226267 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149024. -/
theorem y322TCIndexRepairChecked021 :
    y322TCIndexRepairChecked ⟨149024, by decide⟩ y322TCIndexRepairRaw021
      y322TCIndexRepairAllowed021 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid021
    (hp : ∀ j : Fin 174819, j.val < 149024 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149024, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed021
    y322TCIndexRepairChecked021 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
