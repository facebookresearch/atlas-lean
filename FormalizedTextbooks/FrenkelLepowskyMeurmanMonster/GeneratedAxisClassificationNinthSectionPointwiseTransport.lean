/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionPermutationTransfer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadPointwiseSpatial

/-! The original twelve-letter permutation transports entire positive pointwise isometry groups. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original selected-section word as a genuine positive lattice permutation isometry. -/
def generatedNinthSpreadSectionIsometry : leechIsomSubgroup :=
  golayPermutationIsometry generatedNinthSpreadSectionPermutation

/-- Actual positive coordinate images of the original permutation word. -/
theorem generatedNinth_spread_section_isometry_unit (i : Fin 24) :
    generatedNinthSpreadSectionIsometry.val (Pi.single i 1) =
      Pi.single (generatedNinthSpreadSectionPermutation.val i) 1 := by
  ext j
  have h : generatedNinthSpreadSectionPermutation.val.symm j = i ↔
      j = generatedNinthSpreadSectionPermutation.val i :=
    generatedNinthSpreadSectionPermutation.val.symm_apply_eq
  change golayRealPermute generatedNinthSpreadSectionPermutation.val (Pi.single i 1) j = _
  simp only [golayRealPermute_apply, Pi.single_apply, h]

/-- Actual inverse coordinate images retain the same positive orientation. -/
theorem generatedNinth_spread_section_isometry_inverse_unit (i : Fin 24) :
    generatedNinthSpreadSectionIsometry.val.symm (Pi.single i 1) =
      Pi.single (generatedNinthSpreadSectionPermutation.val.symm i) 1 := by
  have h := congrArg generatedNinthSpreadSectionIsometry.val.symm
    (generatedNinth_spread_section_isometry_unit
      (generatedNinthSpreadSectionPermutation.val.symm i))
  simpa only [LinearEquiv.symm_apply_apply, Equiv.apply_symm_apply] using h.symm

/-- The fixed recovered octad's ordinary bit support agrees with its actual codeword. -/
theorem generatedNinth_section_mask_word : ∀ i : Fin 24,
    (golayEncodedMask generatedNinthSectionCode.val).testBit i.val = true ↔
      golayEncoder (golayLabelCoefficients generatedNinthSectionCode) i = 1 := by
  decide +kernel

/-- All genuine isometries fixing the original Fifth-section coordinates positively. -/
def generatedNinthOriginalSectionPointwiseSpatial : Subgroup leechIsomSubgroup where
  carrier := {g | ∀ i : Fin 24, golayOctadWord generatedFifthFlagOctad i = 1 →
    g.val (Pi.single i 1) = Pi.single i 1}
  one_mem' := by intro i _; rfl
  mul_mem' := by
    intro g h hg hh i hi
    change g.val (h.val (Pi.single i 1)) = Pi.single i 1
    rw [hh i hi, hg i hi]
  inv_mem' := by
    intro g hg i hi
    change g.val.symm (Pi.single i 1) = Pi.single i 1
    have h := congrArg g.val.symm (hg i hi)
    rw [g.val.symm_apply_apply] at h
    exact h.symm

/-- The entire counted spatial group transports to the original coordinate section. -/
def generatedNinthSectionPointwiseEquiv :
    generatedNinthOctadPointwiseSpatial ≃ generatedNinthOriginalSectionPointwiseSpatial where
  toFun g := ⟨generatedNinthSpreadSectionIsometry * g.val *
      generatedNinthSpreadSectionIsometry⁻¹, by
    intro i hi
    let j : Fin 24 := generatedNinthSpreadSectionPermutation.val.symm i
    have hj : (golayEncodedMask generatedNinthSectionCode.val).testBit j.val = true := by
      apply (generatedNinth_section_mask_word j).mpr
      rw [← generatedNinth_spread_section_permutation_support j]
      simpa only [j, Equiv.apply_symm_apply] using hi
    change generatedNinthSpreadSectionIsometry.val
      (g.val.val (generatedNinthSpreadSectionIsometry.val.symm (Pi.single i 1))) = Pi.single i 1
    rw [generatedNinth_spread_section_isometry_inverse_unit, g.property j hj,
      generatedNinth_spread_section_isometry_unit]
    simp only [j, Equiv.apply_symm_apply]⟩
  invFun g := ⟨generatedNinthSpreadSectionIsometry⁻¹ * g.val *
      generatedNinthSpreadSectionIsometry, by
    intro i hi
    have hj : golayOctadWord generatedFifthFlagOctad
        (generatedNinthSpreadSectionPermutation.val i) = 1 := by
      rw [generatedNinth_spread_section_permutation_support]
      exact (generatedNinth_section_mask_word i).mp hi
    change generatedNinthSpreadSectionIsometry.val.symm
      (g.val.val (generatedNinthSpreadSectionIsometry.val (Pi.single i 1))) = Pi.single i 1
    rw [generatedNinth_spread_section_isometry_unit, g.property _ hj,
      generatedNinth_spread_section_isometry_inverse_unit]
    simp only [Equiv.symm_apply_apply]⟩
  left_inv g := by
    apply Subtype.ext
    change generatedNinthSpreadSectionIsometry⁻¹ *
      (generatedNinthSpreadSectionIsometry * g.val * generatedNinthSpreadSectionIsometry⁻¹) *
        generatedNinthSpreadSectionIsometry = g.val
    group
  right_inv g := by
    apply Subtype.ext
    change generatedNinthSpreadSectionIsometry *
      (generatedNinthSpreadSectionIsometry⁻¹ * g.val * generatedNinthSpreadSectionIsometry) *
        generatedNinthSpreadSectionIsometry⁻¹ = g.val
    group

/-- Exactly 512 actual lattice isometries fix the original selected octad positively pointwise. -/
theorem generatedNinth_original_section_pointwise_spatial_card :
    Nat.card generatedNinthOriginalSectionPointwiseSpatial = 512 := by
  rw [← Nat.card_congr generatedNinthSectionPointwiseEquiv,
    generatedNinth_octad_pointwise_spatial_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
