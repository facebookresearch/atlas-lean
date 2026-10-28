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

/-- Literal original-source and earlier-equation contexts replacing instruction 148871. -/
def y322TCIndexRepairRaw005 : List Y322RawContextEquationMove :=
  [
    ⟨77451, true, false,
      [],
      [11]⟩,
    ⟨77296, false, false,
      [77109],
      []⟩,
    ⟨77433, false, false,
      [],
      []⟩,
    ⟨77432, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed005 :
    ∀ move ∈ y322TCIndexRepairRaw005, move.Allowed 48648 226114 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148871. -/
theorem y322TCIndexRepairChecked005 :
    y322TCIndexRepairChecked ⟨148871, by decide⟩ y322TCIndexRepairRaw005
      y322TCIndexRepairAllowed005 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid005
    (hp : ∀ j : Fin 174819, j.val < 148871 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148871, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed005
    y322TCIndexRepairChecked005 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
