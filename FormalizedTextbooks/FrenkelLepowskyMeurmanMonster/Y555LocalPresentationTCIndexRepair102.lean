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

/-- Literal original-source and earlier-equation contexts replacing instruction 149620. -/
def y322TCIndexRepairRaw102 : List Y322RawContextEquationMove :=
  [
    ⟨77256, false, false,
      [722],
      [723, 77329, 5]⟩,
    ⟨79261, true, false,
      [],
      [5]⟩,
    ⟨78048, true, false,
      [],
      [5]⟩,
    ⟨81250, true, false,
      [722],
      [13, 5]⟩,
    ⟨81250, true, false,
      [722],
      [13, 5]⟩,
    ⟨81249, true, false,
      [722],
      [13, 5]⟩,
    ⟨79250, true, false,
      [722],
      [13, 5]⟩,
    ⟨77312, true, false,
      [722, 77253],
      [5]⟩,
    ⟨77311, true, false,
      [722, 77253],
      [5]⟩,
    ⟨81243, false, false,
      [722],
      [5, 5]⟩,
    ⟨77271, false, false,
      [722, 78277],
      []⟩,
    ⟨79249, false, true,
      [],
      [78277]⟩,
    ⟨226661, false, false,
      [721],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed102 :
    ∀ move ∈ y322TCIndexRepairRaw102, move.Allowed 48648 226863 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149620. -/
theorem y322TCIndexRepairChecked102 :
    y322TCIndexRepairChecked ⟨149620, by decide⟩ y322TCIndexRepairRaw102
      y322TCIndexRepairAllowed102 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid102
    (hp : ∀ j : Fin 174819, j.val < 149620 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149620, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed102
    y322TCIndexRepairChecked102 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
