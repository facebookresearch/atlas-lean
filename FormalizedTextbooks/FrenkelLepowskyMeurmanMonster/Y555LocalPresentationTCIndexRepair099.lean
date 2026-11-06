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

/-- Literal original-source and earlier-equation contexts replacing instruction 149608. -/
def y322TCIndexRepairRaw099 : List Y322RawContextEquationMove :=
  [
    ⟨1621, false, false,
      [3112],
      [77321, 15]⟩,
    ⟨1620, false, false,
      [3112, 3109],
      [77321, 15]⟩,
    ⟨81531, true, false,
      [3112, 3109, 1299],
      [15]⟩,
    ⟨80498, true, false,
      [3112, 3109],
      [15]⟩,
    ⟨1619, false, false,
      [3112],
      [77685, 3, 15]⟩,
    ⟨82327, true, false,
      [3112, 3099],
      [3, 15]⟩,
    ⟨83465, true, false,
      [3112],
      [15, 3, 15]⟩,
    ⟨78902, false, false,
      [3112, 79183],
      []⟩,
    ⟨83468, false, false,
      [3112],
      []⟩,
    ⟨83464, false, false,
      [3112],
      []⟩,
    ⟨83473, true, false,
      [],
      [79183]⟩,
    ⟨88306, false, false,
      [3115],
      []⟩,
    ⟨88659, false, false,
      [3115],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed099 :
    ∀ move ∈ y322TCIndexRepairRaw099, move.Allowed 48648 226851 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149608. -/
theorem y322TCIndexRepairChecked099 :
    y322TCIndexRepairChecked ⟨149608, by decide⟩ y322TCIndexRepairRaw099
      y322TCIndexRepairAllowed099 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid099
    (hp : ∀ j : Fin 174819, j.val < 149608 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149608, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed099
    y322TCIndexRepairChecked099 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
