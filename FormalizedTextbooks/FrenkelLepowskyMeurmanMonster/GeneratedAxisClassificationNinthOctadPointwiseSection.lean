/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadPermutationTransport

/-! Exact pointwise permutation order for the actual transported coordinate octad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Golay permutations fixing every physical coordinate of the recovered octad. -/
def generatedNinthSectionOctadPointwise : Subgroup golayAutomorphismSubgroup where
  carrier := {p | ∀ i : Fin 24,
    (golayEncodedMask generatedNinthSectionCode.val).testBit i.val = true → p.val i = i}
  one_mem' := by intro i _; rfl
  mul_mem' := by
    intro p q hp hq i hi
    change p.val (q.val i) = i
    rw [hq i hi, hp i hi]
  inv_mem' := by
    intro p hp i hi
    change p.val.symm i = i
    have h := congrArg p.val.symm (hp i hi)
    rw [p.val.symm_apply_apply] at h
    exact h.symm

/-- Conjugation by the actual octad transport bijects both genuine pointwise permutation groups. -/
def generatedNinthOctadPointwiseEquiv :
    generatedNinthStandardOctadPointwise ≃ generatedNinthSectionOctadPointwise where
  toFun p := ⟨generatedNinthOctadPermutation * p.val * generatedNinthOctadPermutation⁻¹, by
    intro i hi
    let j : Fin 24 := generatedNinthOctadPermutation.val.symm i
    have hj : j.val < 8 := by
      apply (generatedNinth_octad_permutation_support j).mp
      simpa only [j, Equiv.apply_symm_apply] using hi
    have hp : p.val.val j = j := by
      exact p.property ⟨j.val, hj⟩
    change generatedNinthOctadPermutation.val
      (p.val.val (generatedNinthOctadPermutation.val.symm i)) = i
    rw [hp]
    exact generatedNinthOctadPermutation.val.apply_symm_apply i⟩
  invFun p := ⟨generatedNinthOctadPermutation⁻¹ * p.val * generatedNinthOctadPermutation, by
    intro j
    have hj := (generatedNinth_octad_permutation_support (Fin.castAdd 16 j)).mpr j.isLt
    change generatedNinthOctadPermutation.val.symm
      (p.val.val (generatedNinthOctadPermutation.val (Fin.castAdd 16 j))) = Fin.castAdd 16 j
    rw [p.property _ hj]
    exact generatedNinthOctadPermutation.val.symm_apply_apply _⟩
  left_inv p := by
    apply Subtype.ext
    change generatedNinthOctadPermutation⁻¹ *
      (generatedNinthOctadPermutation * p.val * generatedNinthOctadPermutation⁻¹) *
        generatedNinthOctadPermutation = p.val
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  right_inv p := by
    apply Subtype.ext
    change generatedNinthOctadPermutation *
      (generatedNinthOctadPermutation⁻¹ * p.val * generatedNinthOctadPermutation) *
        generatedNinthOctadPermutation⁻¹ = p.val
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

/-- Precisely sixteen actual Golay permutations fix the recovered octad pointwise. -/
theorem generatedNinth_section_octad_pointwise_card :
    Nat.card generatedNinthSectionOctadPointwise = 16 := by
  rw [← Nat.card_congr generatedNinthOctadPointwiseEquiv,
    generatedNinth_standard_octad_pointwise_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
