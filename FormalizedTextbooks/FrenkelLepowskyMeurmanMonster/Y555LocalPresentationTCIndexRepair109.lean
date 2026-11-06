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

/-- Literal original-source and earlier-equation contexts replacing instruction 149659. -/
def y322TCIndexRepairRaw109 : List Y322RawContextEquationMove :=
  [
    ⟨78058, true, false,
      [],
      [13]⟩,
    ⟨78176, true, false,
      [256],
      [9, 13]⟩,
    ⟨78185, false, false,
      [256, 77343],
      []⟩,
    ⟨77290, false, false,
      [256, 77343],
      []⟩,
    ⟨78058, false, false,
      [256],
      []⟩,
    ⟨78075, false, false,
      [256],
      []⟩,
    ⟨78186, false, false,
      [256],
      []⟩,
    ⟨199, true, false,
      [],
      [77341]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed109 :
    ∀ move ∈ y322TCIndexRepairRaw109, move.Allowed 48648 226902 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149659. -/
theorem y322TCIndexRepairChecked109 :
    y322TCIndexRepairChecked ⟨149659, by decide⟩ y322TCIndexRepairRaw109
      y322TCIndexRepairAllowed109 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid109
    (hp : ∀ j : Fin 174819, j.val < 149659 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149659, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed109
    y322TCIndexRepairChecked109 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
