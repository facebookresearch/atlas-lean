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

/-- Literal original-source and earlier-equation contexts replacing instruction 149344. -/
def y322TCIndexRepairRaw066 : List Y322RawContextEquationMove :=
  [
    ⟨77897, false, false,
      [],
      []⟩,
    ⟨77879, true, false,
      [],
      [13]⟩,
    ⟨77470, false, false,
      [77227],
      []⟩,
    ⟨77471, false, false,
      [77227],
      []⟩,
    ⟨77731, false, false,
      [],
      [11]⟩,
    ⟨77876, false, false,
      [103],
      []⟩,
    ⟨77895, false, false,
      [],
      []⟩,
    ⟨77896, false, false,
      [],
      []⟩,
    ⟨77881, false, false,
      [103],
      []⟩,
    ⟨77732, true, false,
      [],
      [77233]⟩,
    ⟨77895, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed066 :
    ∀ move ∈ y322TCIndexRepairRaw066, move.Allowed 48648 226587 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149344. -/
theorem y322TCIndexRepairChecked066 :
    y322TCIndexRepairChecked ⟨149344, by decide⟩ y322TCIndexRepairRaw066
      y322TCIndexRepairAllowed066 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid066
    (hp : ∀ j : Fin 174819, j.val < 149344 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149344, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed066
    y322TCIndexRepairChecked066 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
