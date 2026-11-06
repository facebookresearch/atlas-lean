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

/-- Literal original-source and earlier-equation contexts replacing instruction 149375. -/
def y322TCIndexRepairRaw069 : List Y322RawContextEquationMove :=
  [
    ⟨80421, true, false,
      [244],
      [7]⟩,
    ⟨77281, false, false,
      [244, 77987],
      []⟩,
    ⟨78140, true, false,
      [],
      [77987]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed069 :
    ∀ move ∈ y322TCIndexRepairRaw069, move.Allowed 48648 226618 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149375. -/
theorem y322TCIndexRepairChecked069 :
    y322TCIndexRepairChecked ⟨149375, by decide⟩ y322TCIndexRepairRaw069
      y322TCIndexRepairAllowed069 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid069
    (hp : ∀ j : Fin 174819, j.val < 149375 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149375, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed069
    y322TCIndexRepairChecked069 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
