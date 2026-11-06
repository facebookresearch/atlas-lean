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

/-- Literal original-source and earlier-equation contexts replacing instruction 149505. -/
def y322TCIndexRepairRaw085 : List Y322RawContextEquationMove :=
  [
    ⟨90513, false, false,
      [],
      []⟩,
    ⟨91189, false, false,
      [11893],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed085 :
    ∀ move ∈ y322TCIndexRepairRaw085, move.Allowed 48648 226748 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149505. -/
theorem y322TCIndexRepairChecked085 :
    y322TCIndexRepairChecked ⟨149505, by decide⟩ y322TCIndexRepairRaw085
      y322TCIndexRepairAllowed085 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid085
    (hp : ∀ j : Fin 174819, j.val < 149505 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149505, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed085
    y322TCIndexRepairChecked085 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
