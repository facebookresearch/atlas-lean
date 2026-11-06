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

/-- Literal original-source and earlier-equation contexts replacing instruction 149144. -/
def y322TCIndexRepairRaw038 : List Y322RawContextEquationMove :=
  [
    ⟨77915, false, false,
      [],
      [77171, 15]⟩,
    ⟨77572, true, false,
      [],
      [15]⟩,
    ⟨77572, true, false,
      [],
      [15]⟩,
    ⟨77656, true, false,
      [],
      [15]⟩,
    ⟨77568, true, false,
      [],
      [15]⟩,
    ⟨84963, true, false,
      [],
      [1, 15]⟩,
    ⟨77365, true, false,
      [77167],
      [15]⟩,
    ⟨77364, true, false,
      [77167],
      [15]⟩,
    ⟨40457, true, false,
      [],
      [15, 15]⟩,
    ⟨77244, false, false,
      [80785],
      []⟩,
    ⟨89006, false, false,
      [],
      []⟩,
    ⟨89023, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed038 :
    ∀ move ∈ y322TCIndexRepairRaw038, move.Allowed 48648 226387 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149144. -/
theorem y322TCIndexRepairChecked038 :
    y322TCIndexRepairChecked ⟨149144, by decide⟩ y322TCIndexRepairRaw038
      y322TCIndexRepairAllowed038 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid038
    (hp : ∀ j : Fin 174819, j.val < 149144 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149144, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed038
    y322TCIndexRepairChecked038 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
