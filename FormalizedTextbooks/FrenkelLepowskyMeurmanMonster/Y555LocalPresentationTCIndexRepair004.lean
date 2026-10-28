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

/-- Literal original-source and earlier-equation contexts replacing instruction 148864. -/
def y322TCIndexRepairRaw004 : List Y322RawContextEquationMove :=
  [
    ⟨77434, true, false,
      [],
      [13]⟩,
    ⟨77444, false, false,
      [77107],
      []⟩,
    ⟨77445, false, false,
      [77107],
      []⟩,
    ⟨77443, false, false,
      [],
      [9]⟩,
    ⟨77430, false, false,
      [1],
      []⟩,
    ⟨77442, false, false,
      [1],
      []⟩,
    ⟨77257, true, false,
      [],
      [77109]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed004 :
    ∀ move ∈ y322TCIndexRepairRaw004, move.Allowed 48648 226107 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148864. -/
theorem y322TCIndexRepairChecked004 :
    y322TCIndexRepairChecked ⟨148864, by decide⟩ y322TCIndexRepairRaw004
      y322TCIndexRepairAllowed004 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid004
    (hp : ∀ j : Fin 174819, j.val < 148864 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148864, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed004
    y322TCIndexRepairChecked004 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
