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

/-- Literal original-source and earlier-equation contexts replacing instruction 148996. -/
def y322TCIndexRepairRaw018 : List Y322RawContextEquationMove :=
  [
    ⟨82633, false, false,
      [],
      []⟩,
    ⟨82635, false, false,
      [],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed018 :
    ∀ move ∈ y322TCIndexRepairRaw018, move.Allowed 48648 226239 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148996. -/
theorem y322TCIndexRepairChecked018 :
    y322TCIndexRepairChecked ⟨148996, by decide⟩ y322TCIndexRepairRaw018
      y322TCIndexRepairAllowed018 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid018
    (hp : ∀ j : Fin 174819, j.val < 148996 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148996, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed018
    y322TCIndexRepairChecked018 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
