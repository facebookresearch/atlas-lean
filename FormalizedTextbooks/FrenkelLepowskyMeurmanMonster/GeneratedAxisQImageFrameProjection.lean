/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisQImageInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPointSeparation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCo1FrameOrbit

/-! Actual short-class coverage of a Q image forces its local projection to preserve the frame. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original source Omega is an actual Conway norm-eight point. -/
theorem generatedAxisQImage_omega_point :
    toAdd (qQuotHom sourceOmegaQ) ∈ generatedCo1GeometryPoints := by
  rw [sourceOmegaQ_eq_frame_class]
  exact ⟨_, MulAction.mem_orbit_self _, rfl⟩

/-- Actual short-class coverage leaves Omega as the only norm-eight point in a binary subspace. -/
theorem generatedAxisQImage_unique_omega_of_short_cover
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hcover : ∀ v, v ∈ W → v = 0 ∨ v = toAdd (qQuotHom sourceOmegaQ) ∨
      ∃ r : GriessShortIndex, v = leechHyperbolicCoordinates (griessShortClass r))
    (v : Fin 24 → ZMod 2) (hv : v ∈ W) (hp : v ∈ generatedCo1GeometryPoints) :
    v = toAdd (qQuotHom sourceOmegaQ) := by
  rcases hcover v hv with hz | hw | ⟨r, hr⟩
  · exact False.elim (generatedCo1GeometryPoints_ne_zero v hp hz)
  · exact hw
  · rw [hr] at hp
    exact False.elim (generatedCo1GeometryPoints_short_not_mem r hp)

/-- Short-class coverage of an actual Q intersection forces its Conway projection to fix Omega. -/
theorem generatedAxisQImage_projection_le_frame (K : Subgroup H)
    (hw : toAdd (qQuotHom sourceOmegaQ) ∈ localNormalQImage K)
    (hcover : ∀ v, v ∈ localNormalQImage K →
      v = 0 ∨ v = toAdd (qQuotHom sourceOmegaQ) ∨
        ∃ r : GriessShortIndex, v = leechHyperbolicCoordinates (griessShortClass r)) :
    K.map projH ≤ co1OmegaFrameStabilizer := by
  rintro _ ⟨h, hh, rfl⟩
  exact generatedAxisQImage_unique_frame_fixed K _ hw generatedAxisQImage_omega_point
    (generatedAxisQImage_unique_omega_of_short_cover (localNormalQImage K) hcover) h hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
