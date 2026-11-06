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

/-- Literal original-source and earlier-equation contexts replacing instruction 149523. -/
def y322TCIndexRepairRaw088 : List Y322RawContextEquationMove :=
  [
    ⟨90546, true, false,
      [11916],
      [11]⟩,
    ⟨83784, false, false,
      [11916],
      []⟩,
    ⟨90556, false, false,
      [11916, 3211],
      []⟩,
    ⟨90532, true, false,
      [],
      [3211, 11941, 77285]⟩,
    ⟨90557, true, false,
      [],
      [11941, 77285]⟩,
    ⟨90558, true, false,
      [],
      [77285]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed088 :
    ∀ move ∈ y322TCIndexRepairRaw088, move.Allowed 48648 226766 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149523. -/
theorem y322TCIndexRepairChecked088 :
    y322TCIndexRepairChecked ⟨149523, by decide⟩ y322TCIndexRepairRaw088
      y322TCIndexRepairAllowed088 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid088
    (hp : ∀ j : Fin 174819, j.val < 149523 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149523, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed088
    y322TCIndexRepairChecked088 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
