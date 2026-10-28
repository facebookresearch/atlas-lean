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

/-- Literal original-source and earlier-equation contexts replacing instruction 149598. -/
def y322TCIndexRepairRaw097 : List Y322RawContextEquationMove :=
  [
    ⟨81534, true, false,
      [],
      [13]⟩,
    ⟨77422, false, false,
      [77321],
      []⟩,
    ⟨77423, false, false,
      [77321],
      []⟩,
    ⟨81532, false, false,
      [],
      [5]⟩,
    ⟨78040, false, false,
      [1765],
      []⟩,
    ⟨81539, false, false,
      [1765],
      []⟩,
    ⟨77256, true, false,
      [],
      [1765, 77319]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed097 :
    ∀ move ∈ y322TCIndexRepairRaw097, move.Allowed 48648 226841 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149598. -/
theorem y322TCIndexRepairChecked097 :
    y322TCIndexRepairChecked ⟨149598, by decide⟩ y322TCIndexRepairRaw097
      y322TCIndexRepairAllowed097 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid097
    (hp : ∀ j : Fin 174819, j.val < 149598 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149598, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed097
    y322TCIndexRepairChecked097 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
