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

/-- Literal original-source and earlier-equation contexts replacing instruction 149203. -/
def y322TCIndexRepairRaw048 : List Y322RawContextEquationMove :=
  [
    ⟨89486, false, false,
      [2173, 9630],
      [78637]⟩,
    ⟨81943, true, false,
      [2173, 9630, 9625],
      []⟩,
    ⟨89482, true, false,
      [2173, 9630],
      [5]⟩,
    ⟨82472, true, false,
      [2173, 9630, 1898],
      [5]⟩,
    ⟨81870, false, false,
      [2173, 9630, 1898],
      []⟩,
    ⟨81681, false, false,
      [2173, 9630, 1898],
      []⟩,
    ⟨82473, true, false,
      [2173, 9630],
      [78521]⟩,
    ⟨82471, false, false,
      [2173, 9630],
      []⟩,
    ⟨89117, true, false,
      [2173, 9630],
      [78521]⟩,
    ⟨89487, true, false,
      [2173],
      [1901, 78521]⟩,
    ⟨89488, true, false,
      [2173],
      [78521]⟩,
    ⟨90459, false, false,
      [2173],
      []⟩,
    ⟨90461, false, false,
      [2173, 9635, 11403],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed048 :
    ∀ move ∈ y322TCIndexRepairRaw048, move.Allowed 48648 226446 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149203. -/
theorem y322TCIndexRepairChecked048 :
    y322TCIndexRepairChecked ⟨149203, by decide⟩ y322TCIndexRepairRaw048
      y322TCIndexRepairAllowed048 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid048
    (hp : ∀ j : Fin 174819, j.val < 149203 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149203, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed048
    y322TCIndexRepairChecked048 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
