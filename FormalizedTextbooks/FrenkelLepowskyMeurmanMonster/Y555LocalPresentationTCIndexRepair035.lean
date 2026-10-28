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

/-- Literal original-source and earlier-equation contexts replacing instruction 149123. -/
def y322TCIndexRepairRaw035 : List Y322RawContextEquationMove :=
  [
    ⟨3327, false, false,
      [6524],
      [81173]⟩,
    ⟨77256, false, false,
      [6524, 6522],
      [81173]⟩,
    ⟨85871, true, false,
      [6524, 6522],
      []⟩,
    ⟨77302, true, false,
      [6524, 6522, 81173],
      []⟩,
    ⟨40749, true, false,
      [6524, 6522],
      [13]⟩,
    ⟨3327, false, false,
      [6524, 6522, 6524],
      [81369, 13]⟩,
    ⟨77256, false, false,
      [6524, 6522, 6524, 6522],
      [81369, 13]⟩,
    ⟨77271, true, false,
      [6524, 6522, 6524, 6522, 81369],
      [13]⟩,
    ⟨40749, false, false,
      [6524, 6522, 6524, 6522],
      [5, 5, 13]⟩,
    ⟨77311, false, false,
      [6524, 6522, 6524, 6522, 81173],
      [5, 13]⟩,
    ⟨77312, false, false,
      [6524, 6522, 6524, 6522, 81173],
      [5, 13]⟩,
    ⟨85878, false, false,
      [6524, 6522, 6524, 6522],
      [13, 5, 13]⟩,
    ⟨77657, false, false,
      [6524, 6522, 6524, 6522],
      [13, 5, 13]⟩,
    ⟨77569, false, false,
      [6524, 6522, 6524, 6522],
      [13, 5, 13]⟩,
    ⟨77569, false, false,
      [6524, 6522, 6524, 6522],
      [13, 5, 13]⟩,
    ⟨84964, false, false,
      [6524, 6522, 6524, 6522],
      [5, 13]⟩,
    ⟨84381, false, false,
      [6524, 6522, 6524, 6522],
      [5, 13]⟩,
    ⟨84382, false, false,
      [6524, 6522, 6524, 6522],
      [5, 13]⟩,
    ⟨84382, false, false,
      [6524, 6522, 6524, 6522],
      [5, 13]⟩,
    ⟨86134, false, false,
      [6524, 6522, 6524, 6522],
      [5, 13]⟩,
    ⟨86135, false, false,
      [6524, 6522, 6524, 6522],
      [5, 13]⟩,
    ⟨87933, false, false,
      [6524, 6522, 6524, 6522],
      [5, 13]⟩,
    ⟨82550, true, false,
      [6524, 6522, 6524, 6522, 6521],
      [5, 13]⟩,
    ⟨77341, false, false,
      [6524, 6522, 6524, 6522, 6521, 78847],
      [13]⟩,
    ⟨77342, false, false,
      [6524, 6522, 6524, 6522, 6521, 78847],
      [13]⟩,
    ⟨39488, false, false,
      [6524, 6522, 6524, 6522, 6521],
      [5, 1, 13]⟩,
    ⟨77311, false, false,
      [6524, 6522, 6524, 6522, 6521, 78281],
      [1, 13]⟩,
    ⟨77312, false, false,
      [6524, 6522, 6524, 6522, 6521, 78281],
      [1, 13]⟩,
    ⟨1167, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204],
      [78281, 5, 13, 1, 13]⟩,
    ⟨81986, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204],
      [2203, 78281, 5, 13, 1, 13]⟩,
    ⟨81989, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194],
      [78281, 5, 13, 1, 13]⟩,
    ⟨81265, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 1753],
      [5, 13, 1, 13]⟩,
    ⟨81988, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194],
      [77263, 11, 5, 13, 1, 13]⟩,
    ⟨77271, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 1754, 77263],
      [11, 5, 13, 1, 13]⟩,
    ⟨81987, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 1754],
      [5, 11, 5, 13, 1, 13]⟩,
    ⟨77886, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 78719],
      [5, 13, 1, 13]⟩,
    ⟨77885, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 78719],
      [5, 13, 1, 13]⟩,
    ⟨81984, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194],
      [11, 5, 5, 13, 1, 13]⟩,
    ⟨77387, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 78717],
      [5, 5, 13, 1, 13]⟩,
    ⟨77388, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 78717],
      [5, 5, 13, 1, 13]⟩,
    ⟨81973, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194],
      [3, 5, 5, 13, 1, 13]⟩,
    ⟨79118, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 2183],
      [3, 5, 5, 13, 1, 13]⟩,
    ⟨79280, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 2183, 746],
      [15, 3, 5, 5, 13, 1, 13]⟩,
    ⟨77742, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 2183, 746, 77327],
      [5, 5, 13, 1, 13]⟩,
    ⟨77253, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 2183, 746, 77327],
      [5, 5, 13, 1, 13]⟩,
    ⟨81043, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 2183, 746],
      [5, 5, 13, 1, 13]⟩,
    ⟨439, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 2183],
      [1447, 78243, 5, 5, 13, 1, 13]⟩,
    ⟨795, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194, 2183],
      [78243, 5, 5, 13, 1, 13]⟩,
    ⟨1162, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194],
      [78243, 5, 5, 13, 1, 13]⟩,
    ⟨77256, true, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 2194],
      [2195, 78243, 5, 5, 13, 1, 13]⟩,
    ⟨77271, false, false,
      [6524, 6522, 6524, 6522, 6521, 2204, 78243],
      [13, 1, 13]⟩,
    ⟨1168, true, false,
      [6524, 6522, 6524, 6522, 6521],
      [78243, 13, 1, 13]⟩,
    ⟨39186, false, false,
      [6524, 6522, 6524, 6522, 6521, 2207],
      [13, 1, 13]⟩,
    ⟨77302, false, false,
      [6524, 6522, 6524, 6522, 6521, 2207, 78241],
      [1, 13]⟩,
    ⟨77256, true, false,
      [6524, 6522, 6524, 6522, 6521],
      [2207, 78241, 1, 13]⟩,
    ⟨39185, false, false,
      [6524, 6522, 6524, 6522, 6521, 2207],
      [1, 13]⟩,
    ⟨77251, false, false,
      [6524, 6522, 6524, 6522, 6521, 2207, 78239],
      [13]⟩,
    ⟨77256, true, false,
      [6524, 6522, 6524, 6522, 6521],
      [2207, 78239, 13]⟩,
    ⟨83094, false, false,
      [6524, 6522, 6524, 6522, 6521, 2207],
      [13]⟩,
    ⟨2979, true, false,
      [6524, 6522, 6524, 6522, 6521],
      [77447, 13]⟩,
    ⟨3326, true, false,
      [6524, 6522, 6524, 6522],
      [77447, 13]⟩,
    ⟨3327, false, true,
      [6524, 6522],
      [77447, 13]⟩,
    ⟨78624, false, false,
      [6524],
      []⟩,
    ⟨3327, false, true,
      [],
      [77449]⟩,
    ⟨88736, false, false,
      [6523],
      []⟩
  ]

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- All replacement letters and original-source or chronological references have exact bounds. -/
theorem y322TCIndexRepairAllowed035 :
    ∀ move ∈ y322TCIndexRepairRaw035, move.Allowed 48648 226366 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Exact kernel reduction verifies the finite literal replacement certificate.
/-- Exact contextual replay proves the unchanged literal equation 149123. -/
theorem y322TCIndexRepairChecked035 :
    y322TCIndexRepairChecked ⟨149123, by decide⟩ y322TCIndexRepairRaw035
      y322TCIndexRepairAllowed035 := by
  decide +kernel

/-- The repaired equation follows from original sources and strictly earlier valid equations. -/
theorem y322TCIndexRepairValid035
    (hp : ∀ j : Fin 174819, j.val < 149123 →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram ⟨149123, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322TCIndexRepair_valid _ _ y322TCIndexRepairAllowed035
    y322TCIndexRepairChecked035 hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
