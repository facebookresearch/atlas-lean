/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionBinaryKernel

/-! The original binary root fixer consists of exactly two genuine pointwise orientation cosets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A positive pointwise fixer, optionally followed by the actual negative identity. -/
def generatedNinthSectionBinaryOrientation
    (a : Bool × generatedNinthOriginalSectionPointwiseSpatial) :
    generatedNinthSectionBinaryKernel :=
  if a.1 then ⟨leechNegativeIdentity * a.2.val,
    generatedNinthSectionBinaryKernel.mul_mem generatedNinth_section_negative_mem_kernel
      (generatedNinth_section_pointwise_le_binary_kernel a.2.property)⟩
  else ⟨a.2.val, generatedNinth_section_pointwise_le_binary_kernel a.2.property⟩

/-- Both actual orientation cosets are disjoint and each retains the complete spatial fixer. -/
theorem generatedNinthSectionBinaryOrientation_injective :
    Function.Injective generatedNinthSectionBinaryOrientation := by
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  have he := congrArg Subtype.val h
  cases a <;> cases b
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact he
  · have he : p.val = leechNegativeIdentity * q.val := he
    have hz : leechNegativeIdentity = p.val * q.val⁻¹ := by
      calc
        _ = (leechNegativeIdentity * q.val) * q.val⁻¹ := by group
        _ = _ := by rw [← he]
    have hm := generatedNinthOriginalSectionPointwiseSpatial.mul_mem p.property
      (generatedNinthOriginalSectionPointwiseSpatial.inv_mem q.property)
    rw [← hz] at hm
    exact (generatedNinth_section_negative_not_pointwise hm).elim
  · have he : leechNegativeIdentity * p.val = q.val := he
    have hz : leechNegativeIdentity = q.val * p.val⁻¹ := by
      calc
        _ = (leechNegativeIdentity * p.val) * p.val⁻¹ := by group
        _ = _ := by rw [he]
    have hm := generatedNinthOriginalSectionPointwiseSpatial.mul_mem q.property
      (generatedNinthOriginalSectionPointwiseSpatial.inv_mem p.property)
    rw [← hz] at hm
    exact (generatedNinth_section_negative_not_pointwise hm).elim
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact mul_left_cancel (show leechNegativeIdentity * p.val =
        leechNegativeIdentity * q.val from he)

/-- Every actual binary root fixer has one of the two stated full spatial orientations. -/
theorem generatedNinthSectionBinaryOrientation_surjective :
    Function.Surjective generatedNinthSectionBinaryOrientation := by
  intro g
  rcases generatedNinth_section_binary_kernel_orientations g with hp | hn
  · refine ⟨(false, ⟨g.val, hp⟩), ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨(true, ⟨leechNegativeIdentity * g.val, hn⟩), ?_⟩
    apply Subtype.ext
    change leechNegativeIdentity * (leechNegativeIdentity * g.val) = g.val
    rw [← mul_assoc, generatedNinth_section_negative_square, one_mul]

/-- The entire actual lattice-isometry binary section kernel has exactly 1024 elements. -/
theorem generatedNinth_section_binary_kernel_card :
    Nat.card generatedNinthSectionBinaryKernel = 1024 := by
  rw [← Nat.card_congr (Equiv.ofBijective generatedNinthSectionBinaryOrientation
    ⟨generatedNinthSectionBinaryOrientation_injective,
      generatedNinthSectionBinaryOrientation_surjective⟩), Nat.card_prod,
    generatedNinth_original_section_pointwise_spatial_card]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
