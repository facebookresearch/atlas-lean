/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionBinaryCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionPointwiseTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! The actual binary root fixer contains precisely the two orientations of the positive fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual lattice isometries fixing all eight original root classes modulo twice the lattice. -/
def generatedNinthSectionBinaryKernel : Subgroup leechIsomSubgroup where
  carrier := {g | ∀ j : Fin 8,
    leechModTwoAction g (leechReduction (generatedFifthFrameRoot j)) =
      leechReduction (generatedFifthFrameRoot j)}
  one_mem' := by intro j; rw [map_one]; rfl
  mul_mem' := by
    intro g h hg hh j
    rw [map_mul]
    change leechModTwoAction g
      (leechModTwoAction h (leechReduction (generatedFifthFrameRoot j))) = _
    rw [hh j, hg j]
  inv_mem' := by
    intro g hg j
    rw [map_inv]
    change (leechModTwoAction g).symm (leechReduction (generatedFifthFrameRoot j)) = _
    have h := congrArg (leechModTwoAction g).symm (hg j)
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.symm

/-- Every original physical root expands in the eight positive coordinate vectors. -/
theorem generatedNinth_section_root_coordinate_sum (j : Fin 8) :
    generatedNinthSectionRealRoot j = ∑ k : Fin 8,
      ((generatedOctadIntegerRootMatrix k j : ℝ) / Real.sqrt 8) •
        (Pi.single (generatedFifthFramePositions k) 1 : Fin 24 → ℝ) := by
  rw [generatedNinthSectionRealRoot, generatedFifthFrameRoot_physical]
  ext i
  fin_cases i <;>
    simp [leechCoordinateEmbedding, generatedFifthFrameInsert, generatedFifthFramePositions,
      Fin.sum_univ_succ]

/-- The entire positively fixed coordinate subgroup fixes the actual original binary root
classes. -/
theorem generatedNinth_section_pointwise_le_binary_kernel :
    generatedNinthOriginalSectionPointwiseSpatial ≤ generatedNinthSectionBinaryKernel := by
  intro g hg j
  have hr : g.val (generatedNinthSectionRealRoot j) = generatedNinthSectionRealRoot j := by
    rw [generatedNinth_section_root_coordinate_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, hg _ (generatedFifthFrame_word_positions k)]
  have hu : leechIntegralAction g (generatedFifthFrameRoot j) = generatedFifthFrameRoot j := by
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding]
    exact hr
  change leechReduction (leechIntegralAction g (generatedFifthFrameRoot j)) = _
  rw [hu]

/-- Both genuine central signs fix all original root classes. -/
theorem generatedNinth_section_signs_le_binary_kernel :
    signsSubgroup ≤ generatedNinthSectionBinaryKernel := by
  intro g hg j
  apply leechHyperbolicCoordinates.injective
  rw [← leechBinaryAction_coordinates, leechBinaryAction_sign g hg]
  rfl

/-- The literal negative identity squares to the actual identity isometry. -/
theorem generatedNinth_section_negative_square :
    leechNegativeIdentity * leechNegativeIdentity = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change -(-x) = x
  exact neg_neg x

/-- The actual negative identity belongs to the original binary root fixer. -/
theorem generatedNinth_section_negative_mem_kernel :
    leechNegativeIdentity ∈ generatedNinthSectionBinaryKernel :=
  generatedNinth_section_signs_le_binary_kernel (Or.inr (fun _ => rfl))

/-- Each binary root fixer is positive pointwise, or becomes positive after the actual central
sign. -/
theorem generatedNinth_section_binary_kernel_orientations
    (g : generatedNinthSectionBinaryKernel) :
    g.val ∈ generatedNinthOriginalSectionPointwiseSpatial ∨
      leechNegativeIdentity * g.val ∈ generatedNinthOriginalSectionPointwiseSpatial := by
  rcases generatedNinth_section_binary_uniform_coordinate_sign g.val g.property with hp | hn
  · exact Or.inl hp
  · right
    intro i hi
    change -(g.val.val (Pi.single i 1)) = Pi.single i 1
    rw [hn i hi, neg_neg]

/-- The negative identity is excluded from the positive coordinate fixer by the actual first
unit. -/
theorem generatedNinth_section_negative_not_pointwise :
    leechNegativeIdentity ∉ generatedNinthOriginalSectionPointwiseSpatial := by
  intro h
  have hw : golayOctadWord generatedFifthFlagOctad (0 : Fin 24) = 1 := by
    simp only [golayOctadWord, generatedFifthFlagOctad_label]
    decide +kernel
  have he := congrFun (h 0 hw) 0
  norm_num [leechNegativeIdentity_apply] at he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
