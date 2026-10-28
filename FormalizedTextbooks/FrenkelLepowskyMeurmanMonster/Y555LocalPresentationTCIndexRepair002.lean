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

/-- Literal original-source and earlier-equation contexts replacing instruction 148848. -/
def y322TCIndexRepairRaw002 : List Y322RawContextEquationMove :=
  [
    ⟨77370, true, false,
      [],
      [13]⟩,
    ⟨77390, false, false,
      [77103],
      []⟩,
    ⟨77391, false, false,
      [77103],
      []⟩,
    ⟨77362, false, false,
      [],
      [3]⟩,
    ⟨77356, false, false,
      [],
      [3]⟩,
    ⟨77367, false, false,
      [1],
      []⟩,
    ⟨77377, false, false,
      [1],
      []⟩,
    ⟨77257, true, false,
      [],
      [77105]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed002 :
    ∀ move ∈ y322TCIndexRepairRaw002, move.Allowed 48648 226091 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148848. -/
theorem y322TCIndexRepairChecked002 :
    y322TCIndexRepairChecked ⟨148848, by decide⟩ y322TCIndexRepairRaw002
      y322TCIndexRepairAllowed002 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid002
    (hp : ∀ j : Fin 174819, j.val < 148848 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148848, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed002
    y322TCIndexRepairChecked002 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
