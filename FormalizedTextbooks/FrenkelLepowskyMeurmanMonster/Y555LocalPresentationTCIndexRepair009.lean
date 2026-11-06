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

/-- Literal original-source and earlier-equation contexts replacing instruction 148917. -/
def y322TCIndexRepairRaw009 : List Y322RawContextEquationMove :=
  [
    ⟨77512, true, false,
      [],
      [3]⟩,
    ⟨78427, true, false,
      [322],
      [9, 3]⟩,
    ⟨77816, false, false,
      [322, 77123],
      []⟩,
    ⟨77290, false, false,
      [322, 77123],
      []⟩,
    ⟨78428, false, false,
      [322],
      []⟩,
    ⟨77682, false, false,
      [322],
      []⟩,
    ⟨77515, false, false,
      [322],
      []⟩,
    ⟨77515, false, false,
      [322],
      []⟩,
    ⟨78429, false, false,
      [322],
      []⟩,
    ⟨227, true, false,
      [],
      [77125]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed009 :
    ∀ move ∈ y322TCIndexRepairRaw009, move.Allowed 48648 226160 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148917. -/
theorem y322TCIndexRepairChecked009 :
    y322TCIndexRepairChecked ⟨148917, by decide⟩ y322TCIndexRepairRaw009
      y322TCIndexRepairAllowed009 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid009
    (hp : ∀ j : Fin 174819, j.val < 148917 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148917, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed009
    y322TCIndexRepairChecked009 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
