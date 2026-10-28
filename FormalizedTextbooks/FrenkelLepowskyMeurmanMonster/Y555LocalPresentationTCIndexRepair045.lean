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

/-- Literal original-source and earlier-equation contexts replacing instruction 149192. -/
def y322TCIndexRepairRaw045 : List Y322RawContextEquationMove :=
  [
    ⟨5637, true, true,
      [11142],
      [81191]⟩,
    ⟨77256, false, false,
      [11142, 11144],
      [81191]⟩,
    ⟨85923, true, false,
      [11142, 11144],
      []⟩,
    ⟨77263, true, false,
      [11142, 11144, 81191],
      []⟩,
    ⟨40661, true, false,
      [11142, 11144],
      [3]⟩,
    ⟨5636, false, false,
      [11142, 11144, 11142],
      [81193, 3]⟩,
    ⟨5635, false, false,
      [11142, 11144, 11142],
      [2171, 81193, 3]⟩,
    ⟨81942, false, false,
      [11142, 11144, 11142, 11136],
      [81193, 3]⟩,
    ⟨77302, true, false,
      [11142, 11144, 11142, 11136, 2172, 81193],
      [3]⟩,
    ⟨40661, false, false,
      [11142, 11144, 11142, 11136, 2172],
      [13, 13, 3]⟩,
    ⟨77390, false, false,
      [11142, 11144, 11142, 11136, 2172, 81191],
      [13, 3]⟩,
    ⟨77391, false, false,
      [11142, 11144, 11142, 11136, 2172, 81191],
      [13, 3]⟩,
    ⟨85927, false, false,
      [11142, 11144, 11142, 11136, 2172],
      [3, 13, 3]⟩,
    ⟨85928, false, false,
      [11142, 11144, 11142, 11136, 2172],
      [3, 13, 3]⟩,
    ⟨77650, false, false,
      [11142, 11144, 11142, 11136, 2172],
      [3, 13, 3]⟩,
    ⟨77589, false, false,
      [11142, 11144, 11142, 11136, 2172],
      [3, 13, 3]⟩,
    ⟨77589, false, false,
      [11142, 11144, 11142, 11136, 2172],
      [3, 13, 3]⟩,
    ⟨81948, false, false,
      [11142, 11144, 11142, 11136, 2172],
      [13, 3]⟩,
    ⟨77256, true, false,
      [11142, 11144, 11142, 11136, 2172],
      [2173, 78633, 13, 3]⟩,
    ⟨90001, false, false,
      [11142, 11144, 11142, 11136, 11132],
      [78633, 13, 3]⟩,
    ⟨81948, true, false,
      [11142, 11144, 11142, 11136, 11132, 11129],
      [13, 3]⟩,
    ⟨90000, true, false,
      [11142, 11144, 11142, 11136, 11132],
      [3, 13, 3]⟩,
    ⟨85574, false, false,
      [11142, 11144, 11142, 11136, 11132],
      [13, 3]⟩,
    ⟨89999, false, false,
      [11142, 11144, 11142, 11136, 11132],
      [13, 3]⟩,
    ⟨90002, true, false,
      [11142, 11144, 11142, 11136],
      [11125, 77131, 13, 3]⟩,
    ⟨90003, true, false,
      [11142, 11144, 11142, 11136],
      [77131, 13, 3]⟩,
    ⟨77521, false, false,
      [11142, 11144, 11142],
      [3]⟩,
    ⟨5637, true, false,
      [11142, 11144],
      [77129, 3]⟩,
    ⟨81073, false, false,
      [11142],
      []⟩,
    ⟨5637, true, false,
      [],
      [78259]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed045 :
    ∀ move ∈ y322TCIndexRepairRaw045, move.Allowed 48648 226435 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149192. -/
theorem y322TCIndexRepairChecked045 :
    y322TCIndexRepairChecked ⟨149192, by decide⟩ y322TCIndexRepairRaw045
      y322TCIndexRepairAllowed045 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid045
    (hp : ∀ j : Fin 174819, j.val < 149192 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149192, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed045
    y322TCIndexRepairChecked045 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
