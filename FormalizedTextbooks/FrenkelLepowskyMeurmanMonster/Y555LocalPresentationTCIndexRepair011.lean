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

/-- Literal original-source and earlier-equation contexts replacing instruction 148929. -/
def y322TCIndexRepairRaw011 : List Y322RawContextEquationMove :=
  [
    ⟨77514, true, false,
      [],
      [11]⟩,
    ⟨77296, false, false,
      [77125],
      []⟩,
    ⟨77515, false, false,
      [],
      []⟩,
    ⟨77682, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed011 :
    ∀ move ∈ y322TCIndexRepairRaw011, move.Allowed 48648 226172 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148929. -/
theorem y322TCIndexRepairChecked011 :
    y322TCIndexRepairChecked ⟨148929, by decide⟩ y322TCIndexRepairRaw011
      y322TCIndexRepairAllowed011 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid011
    (hp : ∀ j : Fin 174819, j.val < 148929 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148929, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed011
    y322TCIndexRepairChecked011 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
