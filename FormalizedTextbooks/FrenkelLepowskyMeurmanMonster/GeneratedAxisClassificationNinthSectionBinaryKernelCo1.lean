/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionBinaryKernelCount

/-! Quotienting the actual 1024-element binary root fixer by precisely its two central signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original Conway quotient restricted to the entire actual binary root fixer. -/
def generatedNinthSectionBinaryProjection : generatedNinthSectionBinaryKernel →* Co1 :=
  (QuotientGroup.mk' signsSubgroup).comp generatedNinthSectionBinaryKernel.subtype

/-- The actual image subgroup in the Conway quotient. -/
def generatedNinthSectionBinaryCo1Kernel : Subgroup Co1 :=
  generatedNinthSectionBinaryProjection.range

/-- Both actual central signs included in the original binary root fixer. -/
def generatedNinthSectionBinarySigns : signsSubgroup →* generatedNinthSectionBinaryKernel :=
  signsSubgroup.subtype.codRestrict _ (by
    intro s
    exact generatedNinth_section_signs_le_binary_kernel s.property)

/-- The inclusion retains the exact actual spatial isometry. -/
theorem generatedNinthSectionBinarySigns_injective :
    Function.Injective generatedNinthSectionBinarySigns := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun s : generatedNinthSectionBinaryKernel => s.val) h

/-- The restricted original quotient kernel consists of exactly the included central signs. -/
theorem generatedNinthSectionBinarySigns_range :
    generatedNinthSectionBinarySigns.range = generatedNinthSectionBinaryProjection.ker := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    change QuotientGroup.mk s.val = (1 : Co1)
    exact (QuotientGroup.eq_one_iff _).mpr s.property
  · intro h
    have hs : g.val ∈ signsSubgroup := (QuotientGroup.eq_one_iff _).mp h
    exact ⟨⟨g.val, hs⟩, Subtype.ext rfl⟩

/-- Exactly two actual spatial isometries lie in the restricted original quotient kernel. -/
theorem generatedNinth_section_binary_projection_kernel_card :
    Nat.card generatedNinthSectionBinaryProjection.ker = 2 := by
  rw [← generatedNinthSectionBinarySigns_range]
  have he := Nat.card_congr
    (MonoidHom.ofInjective generatedNinthSectionBinarySigns_injective).toEquiv
  rw [← he]
  exact signsSubgroup_card

/-- The full actual Conway binary section kernel has exactly 512 elements. -/
theorem generatedNinth_section_binary_co1_kernel_card :
    Nat.card generatedNinthSectionBinaryCo1Kernel = 512 := by
  have h := generatedNinthSectionBinaryProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedNinth_section_binary_projection_kernel_card] at h
  change 2 * Nat.card generatedNinthSectionBinaryCo1Kernel =
    Nat.card generatedNinthSectionBinaryKernel at h
  rw [generatedNinth_section_binary_kernel_card] at h
  omega

/-- Membership is precisely fixation of every genuine original root class in the actual action. -/
theorem generatedNinth_section_binary_co1_kernel_mem_iff (g : Co1) :
    g ∈ generatedNinthSectionBinaryCo1Kernel ↔ ∀ j : Fin 8,
      co1BinaryAction g (leechHyperbolicCoordinates (leechReduction (generatedFifthFrameRoot j))) =
        leechHyperbolicCoordinates (leechReduction (generatedFifthFrameRoot j)) := by
  constructor
  · rintro ⟨e, rfl⟩ j
    change leechBinaryAction e.val
      (leechHyperbolicCoordinates (leechReduction (generatedFifthFrameRoot j))) = _
    rw [leechBinaryAction_coordinates, e.property j]
  · intro h
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective signsSubgroup g
    have he : e ∈ generatedNinthSectionBinaryKernel := by
      intro j
      apply leechHyperbolicCoordinates.injective
      rw [← leechBinaryAction_coordinates]
      exact h j
    exact ⟨⟨e, he⟩, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
