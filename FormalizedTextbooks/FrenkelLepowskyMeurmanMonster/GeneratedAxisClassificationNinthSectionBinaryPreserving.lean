/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionBinaryKernel

/-! The actual binary root kernel preserves the entire original integral E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Binary root fixation preserves support for every vector of the original integral section. -/
theorem generatedNinth_section_binary_supported_image (g : leechIsomSubgroup)
    (hg : g ∈ generatedNinthSectionBinaryKernel) (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    generatedOctadSupported (golayOctadWord generatedFifthFlagOctad)
      (leechIntegralAction g u).val := by
  rcases generatedNinth_section_binary_uniform_root_sign g hg with hp | hn
  · have hs : ∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) =
        (1 : ℝ) • generatedNinthSectionRealRoot j := by simpa only [one_smul] using hp
    have he := generatedNinth_section_scalar_supported g 1 hs u hu
    have hf : leechIntegralAction g u = u := by
      apply Subtype.ext
      apply leechCoordinateEmbedding_injective
      rw [leechIntegralAction_embedding]
      simpa only [one_smul] using he
    rwa [hf]
  · have hs : ∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) =
        (-1 : ℝ) • generatedNinthSectionRealRoot j := by simpa only [neg_one_smul] using hn
    have he := generatedNinth_section_scalar_supported g (-1) hs u hu
    have hf : leechIntegralAction g u = -u := by
      apply Subtype.ext
      apply leechCoordinateEmbedding_injective
      rw [leechIntegralAction_embedding, Submodule.coe_neg, map_neg]
      simpa only [neg_one_smul] using he
    rw [hf]
    intro i hi
    change -(u.val i) = 0
    rw [hu i hi, neg_zero]

/-- Fixing the original binary roots preserves the actual integral section in both directions. -/
theorem generatedNinth_section_binary_preserves (g : leechIsomSubgroup)
    (hg : g ∈ generatedNinthSectionBinaryKernel) :
    generatedOctadPreserves (golayOctadWord generatedFifthFlagOctad) g := by
  intro u
  constructor
  · intro hu
    have h := generatedNinth_section_binary_supported_image g⁻¹
      (generatedNinthSectionBinaryKernel.inv_mem hg) (leechIntegralAction g u) hu
    rw [map_inv] at h
    change generatedOctadSupported (golayOctadWord generatedFifthFlagOctad)
      ((leechIntegralAction g).symm ((leechIntegralAction g) u)).val at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  · exact generatedNinth_section_binary_supported_image g hg u

/-- The whole actual binary root kernel is contained in the full original section stabilizer. -/
theorem generatedNinth_section_binary_kernel_le_section :
    generatedNinthSectionBinaryKernel ≤
      generatedAxisE8SectionStabilizer (golayOctadWord generatedFifthFlagOctad) := by
  intro g hg
  rw [generatedAxisE8SectionStabilizer_mem]
  exact generatedAxisE8_preserving_image _ _ (generatedNinth_section_binary_preserves g hg)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
