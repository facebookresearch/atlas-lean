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

/-- Literal original-source and earlier-equation contexts replacing instruction 149325. -/
def y322TCIndexRepairRaw064 : List Y322RawContextEquationMove :=
  [
    ⟨77635, true, false,
      [],
      [7]⟩,
    ⟨77632, true, false,
      [],
      [7]⟩,
    ⟨77383, false, false,
      [77227],
      []⟩,
    ⟨77384, false, false,
      [77227],
      []⟩,
    ⟨77729, false, false,
      [],
      [3]⟩,
    ⟨77632, false, false,
      [97],
      []⟩,
    ⟨77730, true, false,
      [],
      [77225]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed064 :
    ∀ move ∈ y322TCIndexRepairRaw064, move.Allowed 48648 226568 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149325. -/
theorem y322TCIndexRepairChecked064 :
    y322TCIndexRepairChecked ⟨149325, by decide⟩ y322TCIndexRepairRaw064
      y322TCIndexRepairAllowed064 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid064
    (hp : ∀ j : Fin 174819, j.val < 149325 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149325, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed064
    y322TCIndexRepairChecked064 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
