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

/-- Literal original-source and earlier-equation contexts replacing instruction 149199. -/
def y322TCIndexRepairRaw047 : List Y322RawContextEquationMove :=
  [
    ⟨90113, true, false,
      [11210],
      [9]⟩,
    ⟨78042, false, false,
      [11210],
      []⟩,
    ⟨81531, false, false,
      [11210],
      []⟩,
    ⟨90116, true, false,
      [],
      [1759, 77321]⟩,
    ⟨90117, true, false,
      [],
      [77321]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed047 :
    ∀ move ∈ y322TCIndexRepairRaw047, move.Allowed 48648 226442 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149199. -/
theorem y322TCIndexRepairChecked047 :
    y322TCIndexRepairChecked ⟨149199, by decide⟩ y322TCIndexRepairRaw047
      y322TCIndexRepairAllowed047 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid047
    (hp : ∀ j : Fin 174819, j.val < 149199 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149199, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed047
    y322TCIndexRepairChecked047 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
