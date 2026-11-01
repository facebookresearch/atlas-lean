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

/-- Literal original-source and earlier-equation contexts replacing instruction 149184. -/
def y322TCIndexRepairRaw044 : List Y322RawContextEquationMove :=
  [
    ⟨3564, false, false,
      [6998],
      [81185]⟩,
    ⟨77256, false, false,
      [6998, 6996],
      [81185]⟩,
    ⟨85913, true, false,
      [6998, 6996],
      []⟩,
    ⟨77915, false, false,
      [6998, 6996],
      [81185]⟩,
    ⟨85914, true, false,
      [6998, 6996],
      []⟩,
    ⟨85914, true, false,
      [6998, 6996],
      []⟩,
    ⟨85913, true, false,
      [6998, 6996],
      []⟩,
    ⟨85921, true, false,
      [6998, 6996],
      []⟩,
    ⟨77582, true, false,
      [6998, 6996],
      [15]⟩,
    ⟨77582, true, false,
      [6998, 6996],
      [15]⟩,
    ⟨77652, true, false,
      [6998, 6996],
      [15]⟩,
    ⟨77582, true, false,
      [6998, 6996],
      [15]⟩,
    ⟨77289, true, false,
      [6998, 6996, 77181],
      [15]⟩,
    ⟨86713, false, false,
      [6998, 6996],
      [9, 15]⟩,
    ⟨77291, true, false,
      [6998, 6996, 81955],
      []⟩,
    ⟨77288, true, false,
      [6998, 6996, 81955],
      []⟩,
    ⟨41228, true, false,
      [6998, 6996],
      [9]⟩,
    ⟨3562, false, false,
      [6998, 6996, 6994],
      [82327, 9]⟩,
    ⟨77256, false, false,
      [6998, 6996, 6994, 6992],
      [82327, 9]⟩,
    ⟨41228, false, false,
      [6998, 6996, 6994, 6992],
      [9]⟩,
    ⟨88061, false, false,
      [6998, 6996, 6994, 6992],
      [15, 9]⟩,
    ⟨83156, false, false,
      [6998, 6996, 6994, 6992, 6989],
      [9]⟩,
    ⟨83168, false, false,
      [6998, 6996, 6994, 6992, 6989, 2749],
      [9]⟩,
    ⟨1472, true, false,
      [6998, 6996, 6994, 6992, 6989],
      [78111, 9]⟩,
    ⟨3561, true, false,
      [6998, 6996, 6994, 6992],
      [78111, 9]⟩,
    ⟨3562, false, true,
      [6998, 6996],
      [78111, 9]⟩,
    ⟨83165, true, false,
      [6998, 6996, 6993, 2768],
      [9]⟩,
    ⟨80836, false, false,
      [6998, 6996, 6993, 2768],
      []⟩,
    ⟨80838, false, false,
      [6998, 6996, 6993, 2768],
      []⟩,
    ⟨83167, true, false,
      [6998, 6996, 6993],
      [78115]⟩,
    ⟨83167, true, false,
      [6998, 6996, 6993],
      [78115]⟩,
    ⟨83166, true, false,
      [6998, 6996, 6993],
      [78115]⟩,
    ⟨3563, true, false,
      [6998, 6996],
      [78115]⟩,
    ⟨3564, false, true,
      [],
      [78115]⟩,
    ⟨88073, false, false,
      [6997, 7032],
      [78115]⟩,
    ⟨88067, false, false,
      [6997, 7032],
      [6291, 78115]⟩,
    ⟨87861, true, false,
      [6997, 7032, 7028],
      []⟩,
    ⟨86726, true, false,
      [6997, 7032, 7028],
      []⟩,
    ⟨77296, true, false,
      [6997, 7032, 7028, 81963],
      []⟩,
    ⟨86730, false, false,
      [6997, 7032, 7028],
      [11]⟩,
    ⟨88072, false, false,
      [6997, 7032, 7028],
      []⟩,
    ⟨88074, true, false,
      [6997],
      [77155]⟩,
    ⟨88467, false, false,
      [6997, 7035],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed044 :
    ∀ move ∈ y322TCIndexRepairRaw044, move.Allowed 48648 226427 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149184. -/
theorem y322TCIndexRepairChecked044 :
    y322TCIndexRepairChecked ⟨149184, by decide⟩ y322TCIndexRepairRaw044
      y322TCIndexRepairAllowed044 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid044
    (hp : ∀ j : Fin 174819, j.val < 149184 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149184, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed044
    y322TCIndexRepairChecked044 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
