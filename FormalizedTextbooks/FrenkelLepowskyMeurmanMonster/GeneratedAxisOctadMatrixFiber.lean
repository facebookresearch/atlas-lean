/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadQOrbitCount

/-! The genuine matrix fiber of the octad-image H orbit is its actual 256-axis Q orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual local-orbit points with the same physical matrix as the octad-image axis. -/
def generatedOctadMatrixFiber (e : Fin 64) (c : ZMod 2) : Set GriessSpace :=
  {x | x ∈ MulAction.orbit H (generatedOctadLocalAxis e c) ∧
    (griessConwayEncode x).1 = (griessConwayEncode (generatedOctadLocalAxis e c)).1}

/-- An actual H element over the section stabilizer differs from an axis-fixing lift by Q. -/
theorem generatedOctad_projected_phase_factorization (e : Fin 64) (c : ZMod 2) (h : H)
    (hp : projH h ∈
      generatedAxisE8Co1SectionStabilizer (golayOctadWord generatedOctadBasisOctad)) :
    ∃ q : Q, rhoLocal (inclQ q) (generatedOctadLocalAxis e c) =
      rhoLocal h (generatedOctadLocalAxis e c) := by
  obtain ⟨k, hk⟩ := generatedOctadLocalAxisProjection_surjective e c ⟨projH h, hp⟩
  have he : projH k.val = projH h := congrArg Subtype.val hk
  have hker : h * k.val⁻¹ ∈ projH.ker := by
    change projH (h * k.val⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [← inclQ_range_eq_projH_ker] at hker
  obtain ⟨q, hq⟩ := hker
  have hfix : k.val⁻¹ • generatedOctadLocalAxis e c = generatedOctadLocalAxis e c := by
    rw [inv_smul_eq_iff]
    exact k.property.symm
  refine ⟨q, ?_⟩
  rw [hq]
  change (h * k.val⁻¹) • generatedOctadLocalAxis e c = h • generatedOctadLocalAxis e c
  rw [mul_smul, hfix]

/-- Equal physical matrix coordinates force an actual local-orbit point into the Q phase orbit. -/
theorem generatedOctadMatrixFiber_eq_phase_orbit (e : Fin 64) (c : ZMod 2) :
    generatedOctadMatrixFiber e c = generatedOctadQAxisOrbit e c := by
  ext x
  constructor
  · rintro ⟨⟨h, hh⟩, hmatrix⟩
    change h • generatedOctadLocalAxis e c = x at hh
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
    change localFiberIntoH f = h at hf
    have hm : (griessConwayEncode
        (rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis e c))).1 =
        (griessConwayEncode (generatedOctadLocalAxis e c)).1 := by
      rw [hf]
      change (griessConwayEncode (h • generatedOctadLocalAxis e c)).1 = _
      rw [hh]
      exact hmatrix
    change (griessConwayEncode (localGriessRepresentation f _)).1 = _ at hm
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at hm
    have hg : f.val.2 ∈
        generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad) := by
      rw [generatedAxisE8SectionStabilizer_mem]
      apply (generatedAxisE8_matrix_action_iff_section_stabilizer _ _).mp
      rw [generatedOctad_section_projection_eq_matrix e c]
      exact hm
    have hp : projH h ∈
        generatedAxisE8Co1SectionStabilizer (golayOctadWord generatedOctadBasisOctad) := by
      refine ⟨f.val.2, hg, ?_⟩
      change QuotientGroup.mk' signsSubgroup f.val.2 = projH h
      rw [← hf]
      rfl
    obtain ⟨q, hq⟩ := generatedOctad_projected_phase_factorization e c h hp
    exact ⟨q, hq.trans hh⟩
  · rintro ⟨q, rfl⟩
    refine ⟨⟨inclQ q, rfl⟩, ?_⟩
    change (griessConwayEncode
      (localGriessRepresentation (localFiberIncl q) (generatedOctadLocalAxis e c))).1 = _
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl

/-- Exactly 256 actual local axes share this genuine physical matrix projection. -/
theorem generatedOctadMatrixFiber_card (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedOctadMatrixFiber e c) = 256 := by
  rw [generatedOctadMatrixFiber_eq_phase_orbit, generatedOctadQAxisOrbit_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
