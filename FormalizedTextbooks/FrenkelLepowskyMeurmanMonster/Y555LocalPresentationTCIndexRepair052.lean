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

/-- Literal original-source and earlier-equation contexts replacing instruction 149227. -/
def y322TCIndexRepairRaw052 : List Y322RawContextEquationMove :=
  [
    ⟨89477, true, false,
      [9624],
      [13]⟩,
    ⟨81654, true, false,
      [9624],
      [13]⟩,
    ⟨77302, false, false,
      [9624, 78419],
      []⟩,
    ⟨81645, false, false,
      [9624],
      []⟩,
    ⟨81644, false, false,
      [9624],
      []⟩,
    ⟨89479, true, false,
      [],
      [78419]⟩,
    ⟨89480, true, false,
      [],
      [78419]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed052 :
    ∀ move ∈ y322TCIndexRepairRaw052, move.Allowed 48648 226470 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149227. -/
theorem y322TCIndexRepairChecked052 :
    y322TCIndexRepairChecked ⟨149227, by decide⟩ y322TCIndexRepairRaw052
      y322TCIndexRepairAllowed052 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid052
    (hp : ∀ j : Fin 174819, j.val < 149227 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149227, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed052
    y322TCIndexRepairChecked052 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
