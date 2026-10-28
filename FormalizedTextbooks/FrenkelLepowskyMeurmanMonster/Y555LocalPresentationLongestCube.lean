/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine original-Y555 longest-word cubic from the original C431 source certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431LongestCube

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual local-source map agrees with the literal independent-Y555 generator evaluation. -/
theorem y431IntoY555_comp_mk :
    y431IntoY555.comp (PresentedGroup.mk y431Relations) =
      FreeGroup.lift (fun v =>
        (PresentedGroup.of (y431Vertex v) : BimonsterPresentation)) := by
  apply FreeGroup.ext_hom
  intro v
  change y431IntoY555 (PresentedGroup.of v) =
    FreeGroup.lift (fun v =>
      (PresentedGroup.of (y431Vertex v) : BimonsterPresentation)) (FreeGroup.of v)
  rw [FreeGroup.lift_apply_of]
  exact y431IntoY555_generator v

/-- The literal corrected longest involution and e1 satisfy the cubic in independent Y555. -/
theorem y555LocalF1_e1_cube :
    (y555LocalF1 * (PresentedGroup.of (some (0, 3)) : BimonsterPresentation)) ^ 3 = 1 := by
  have h := congrArg y431IntoY555 y431LongestCube_eq_one
  have he : FreeGroup.lift
      (fun v => (PresentedGroup.of (y431Vertex v) : BimonsterPresentation))
      y431LongestCube = 1 := by
    rw [← y431IntoY555_comp_mk]
    simpa only [MonoidHom.comp_apply, map_one] using h
  rwa [y431LongestCube_source_value] at he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
