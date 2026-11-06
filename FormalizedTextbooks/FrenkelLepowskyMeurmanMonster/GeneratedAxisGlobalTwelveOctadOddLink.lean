/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadDestination

/-! The actual Octad-to-Odd transition, from the proved odd root-six transport and the singleton
cocode triality exchange, and the reduction of Octad-family coverage to the octad-diagonal binding
alone. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The singleton cocode element after the inverse of the proved odd root-six transport is an
octad-family transition of Odd class. -/
theorem generatedAxisGlobalTwelveOctad_oddLink : GeneratedAxisGlobalTwelveOctadOddLink := by
  obtain ⟨h, hh⟩ := generatedAxisGlobalOddRoot06PositiveOctad_transporter
  refine ⟨inclQ singletonCocodeQ * h⁻¹, ?_⟩
  have hu : rhoLocal h⁻¹ (generatedOctadLocalAxis 0 0) =
      sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis) := by
    rw [generatedAxisGlobalTwelveOctad_axis_eq, ← hh, map_inv]
    exact LinearEquiv.symm_apply_apply _ _
  have hs : sExtra⁻¹
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)) =
        rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis :=
    LinearEquiv.symm_apply_apply _ _
  rw [map_mul, LinearEquiv.mul_apply, hu, generatedAxisGlobal_singleton_triality_exchange, hs,
    generatedAxisGlobalTwelveOctadClass_local, generatedAxisGlobalTwelveOctadClass_local]

/-- Under the octad-diagonal binding, every actual Octad-family transition lies in the twelve-family
catalogue union. -/
theorem generatedAxisGlobalTwelve_octad_covered_of
    (hdiag : GeneratedAxisGlobalTwelveOctadDiagonalBound) :
    GeneratedAxisGlobalTwelveFamilyCovered 1 :=
  generatedAxisGlobalTwelve_octad_covered_of_links hdiag generatedAxisGlobalTwelveOctad_oddLink

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
