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

/-- Literal original-source and earlier-equation contexts replacing instruction 148986. -/
def y322TCIndexRepairRaw017 : List Y322RawContextEquationMove :=
  [
    ⟨82340, false, false,
      [],
      []⟩,
    ⟨82343, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed017 :
    ∀ move ∈ y322TCIndexRepairRaw017, move.Allowed 48648 226229 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148986. -/
theorem y322TCIndexRepairChecked017 :
    y322TCIndexRepairChecked ⟨148986, by decide⟩ y322TCIndexRepairRaw017
      y322TCIndexRepairAllowed017 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid017
    (hp : ∀ j : Fin 174819, j.val < 148986 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148986, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed017
    y322TCIndexRepairChecked017 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
