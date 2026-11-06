/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseCoordinates

/-! The packed frame orbit uses the actual norm-eight coordinate frame carrier. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The initial packed vector is precisely the binary class of the original coordinate frame. -/
theorem sixthFrameOrbitBase_actual_frame :
    sixthFrameOrbitBase = monsterCo1GeometryBasePoint.val := by
  rw [monsterCo1GeometryBasePoint_binary]
  change monsterCo1GeometryBinaryMaskDecode 2048 = Pi.single 11 (1 : ZMod 2)
  decide +kernel

/-- Every actual Conway translate of the initial vector lies in the original frame-class carrier. -/
theorem sixthFrameOrbit_orbit_actual_frames (K : Subgroup Co1) (v : Fin 24 → ZMod 2)
    (hv : v ∈ MulAction.orbit K sixthFrameOrbitBase) : v ∈ generatedCo1GeometryPoints := by
  obtain ⟨g, hg⟩ := hv
  change co1BinaryAction g.val sixthFrameOrbitBase = v at hg
  rw [← hg, sixthFrameOrbitBase_actual_frame]
  exact generatedCo1GeometryPoints_action g.val _ monsterCo1GeometryBasePoint.property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
