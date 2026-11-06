/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightEnumeration

/-! Every actual coordinate E8 section has exactly 2160 genuine norm-eight vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The bounded source enumeration is a genuine bijection. -/
def generatedOctadNormEightEnumerationEquiv :
    (Σ b : ZMod 2, GeneratedOctadNormEightBounded b) ≃
      GeneratedOctadNormEight golayStandardOctad :=
  Equiv.ofBijective generatedOctadBoundedVector
    ⟨generatedOctadBoundedVector_injective, generatedOctadBoundedVector_surjective⟩

/-- Exact cardinality of the actual standard coordinate section. -/
theorem generatedStandardOctad_normEight_card :
    Nat.card (GeneratedOctadNormEight golayStandardOctad) = 2160 := by
  rw [Nat.card_congr generatedOctadNormEightEnumerationEquiv.symm, Nat.card_sigma]
  change Nat.card (GeneratedOctadNormEightBounded 0) +
    Nat.card (GeneratedOctadNormEightBounded 1) = 2160
  rw [generatedOctadNormEightBounded_zero_card, generatedOctadNormEightBounded_one_card]

/-- A genuine Golay permutation gives a bijection of the actual norm-eight section vectors. -/
def generatedOctadNormEightPermutationEquiv (c d : Fin 24 → ZMod 2)
    (p : golayAutomorphismSubgroup) (hp : golayPermute p.val c = d) :
    GeneratedOctadNormEight c ≃ GeneratedOctadNormEight d where
  toFun x := ⟨leechIntegralAction (golayPermutationIsometry p) x.val,
    (generatedOctadSupported_permutation c d p hp x.val).mpr x.property.1,
    by rw [leechIntegralAction_squareSum]; exact x.property.2⟩
  invFun y := ⟨leechIntegralAction (golayPermutationIsometry p)⁻¹ y.val, by
    have h := generatedOctadSupported_permutation c d p hp
      (leechIntegralAction (golayPermutationIsometry p)⁻¹ y.val)
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
    exact h.mp y.property.1,
    by rw [leechIntegralAction_squareSum]; exact y.property.2⟩
  left_inv x := by
    apply Subtype.ext
    change leechIntegralAction (golayPermutationIsometry p)⁻¹
      (leechIntegralAction (golayPermutationIsometry p) x.val) = x.val
    rw [map_inv]
    exact (leechIntegralAction (golayPermutationIsometry p)).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    change leechIntegralAction (golayPermutationIsometry p)
      (leechIntegralAction (golayPermutationIsometry p)⁻¹ y.val) = y.val
    rw [map_inv]
    exact (leechIntegralAction (golayPermutationIsometry p)).apply_symm_apply y.val

/-- Every actual coordinate Golay octad contains exactly 2160 norm-eight lattice vectors. -/
theorem generatedOctad_normEight_card (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8) :
    Nat.card (GeneratedOctadNormEight c) = 2160 := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard c hc hw
  rw [Nat.card_congr (generatedOctadNormEightPermutationEquiv c golayStandardOctad p hp)]
  exact generatedStandardOctad_normEight_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
