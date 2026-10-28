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

/-- Literal original-source and earlier-equation contexts replacing instruction 148882. -/
def y322TCIndexRepairRaw006 : List Y322RawContextEquationMove :=
  [
    ⟨77487, true, false,
      [],
      [1]⟩,
    ⟨77487, true, false,
      [],
      [1]⟩,
    ⟨77486, true, false,
      [],
      [1]⟩,
    ⟨77485, true, false,
      [],
      [1]⟩,
    ⟨77489, false, false,
      [77113],
      []⟩,
    ⟨77492, false, false,
      [77113],
      []⟩,
    ⟨77478, false, false,
      [],
      [13, 1, 13]⟩,
    ⟨77453, false, false,
      [],
      [13, 1, 13]⟩,
    ⟨77454, false, false,
      [],
      [13, 1, 13]⟩,
    ⟨77454, false, false,
      [],
      [13, 1, 13]⟩,
    ⟨77472, false, false,
      [],
      [1, 13]⟩,
    ⟨77469, false, false,
      [],
      [1, 13]⟩,
    ⟨77477, false, false,
      [1],
      [13]⟩,
    ⟨77483, false, false,
      [1],
      []⟩,
    ⟨77493, false, false,
      [1],
      []⟩,
    ⟨77257, true, false,
      [],
      [77115]⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed006 :
    ∀ move ∈ y322TCIndexRepairRaw006, move.Allowed 48648 226125 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 148882. -/
theorem y322TCIndexRepairChecked006 :
    y322TCIndexRepairChecked ⟨148882, by decide⟩ y322TCIndexRepairRaw006
      y322TCIndexRepairAllowed006 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid006
    (hp : ∀ j : Fin 174819, j.val < 148882 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨148882, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed006
    y322TCIndexRepairChecked006 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
