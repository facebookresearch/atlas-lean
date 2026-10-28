/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Cyclic cubic and commutation consequences of the proved original-source C431 certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationLongestCube

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The third-arm longest word is the second actual cyclic image of the original F1. -/
def y555LocalF3 : BimonsterPresentation := y555CycleHom y555LocalF2

/-- The second-arm cubic is the cyclic image of the proved original-source first-arm cubic. -/
theorem y555LocalF2_e2_cube :
    (y555LocalF2 * (PresentedGroup.of (some (1, 3)) : BimonsterPresentation)) ^ 3 = 1 := by
  have h := congrArg y555CycleHom y555LocalF1_e1_cube
  have hv : y555VertexCycle (some (0, 3)) = some (1, 3) := by decide +kernel
  simpa only [map_pow, map_mul, map_one, y555LocalF2, y555CycleHom_generator, hv] using h

/-- The third-arm cubic is the cyclic image of the proved second-arm cubic. -/
theorem y555LocalF3_e3_cube :
    (y555LocalF3 * (PresentedGroup.of (some (2, 3)) : BimonsterPresentation)) ^ 3 = 1 := by
  have h := congrArg y555CycleHom y555LocalF2_e2_cube
  have hv : y555VertexCycle (some (1, 3)) = some (2, 3) := by decide +kernel
  simpa only [map_pow, map_mul, map_one, y555LocalF3, y555CycleHom_generator, hv] using h

/-- The third longest word is an involution under the genuine cyclic source map. -/
theorem y555LocalF3_square : y555LocalF3 * y555LocalF3 = 1 := by
  simpa only [y555LocalF3, map_mul, map_one] using
    congrArg y555CycleHom y555LocalF2_square

/-- A second-arm longest word commutes with every original vertex except its own e2. -/
theorem y555LocalF2_commute (v : Y555Vertex) (hv : v ≠ some (1, 3)) :
    Commute y555LocalF2 (PresentedGroup.of v) := by
  let u := y555VertexCycle (y555VertexCycle v)
  have hu : u ≠ some (0, 3) := by
    intro he
    have h := congrArg y555VertexCycle he
    have hc : y555VertexCycle (some (0, 3)) = some (1, 3) := by decide +kernel
    exact hv (by simpa only [u, y555VertexCycle_three, hc] using h)
  have h := (y555LocalF1_commute u hu).map y555CycleHom
  simpa only [u, y555LocalF2, y555CycleHom_generator, y555VertexCycle_three] using h

/-- A third-arm longest word commutes with every original vertex except its own e3. -/
theorem y555LocalF3_commute (v : Y555Vertex) (hv : v ≠ some (2, 3)) :
    Commute y555LocalF3 (PresentedGroup.of v) := by
  let u := y555VertexCycle (y555VertexCycle v)
  have hu : u ≠ some (1, 3) := by
    intro he
    have h := congrArg y555VertexCycle he
    have hc : y555VertexCycle (some (1, 3)) = some (2, 3) := by decide +kernel
    exact hv (by simpa only [u, y555VertexCycle_three, hc] using h)
  have h := (y555LocalF2_commute u hu).map y555CycleHom
  simpa only [u, y555LocalF3, y555CycleHom_generator, y555VertexCycle_three] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
