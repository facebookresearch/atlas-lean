/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8AffineData

/-! Complete actual pointwise-octad permutation coverage and the outside-line permutation kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The sixteen already counted actual standard representatives cover the entire subgroup. -/
theorem generatedTenth_e8_standard_affine_surjective :
    Function.Surjective generatedNinthStandardOctadElement := by
  have hcard : Nat.card (Fin 16) = Nat.card generatedNinthStandardOctadPointwise := by
    rw [Nat.card_fin, generatedNinth_standard_octad_pointwise_card]
  exact ((Nat.bijective_iff_injective_and_card generatedNinthStandardOctadElement).mpr
    ⟨generatedNinthStandardOctadElement_injective, hcard⟩).surjective

private theorem affine_coverage_of_transport (p q : golayAutomorphismSubgroup)
    (hsupport : ∀ i : Fin 24, p.val i ∈ generatedTenthE7OctadSupport ↔ i.val < 8)
    (hq : ∀ i ∈ generatedTenthE7OctadSupport, q.val i = i) :
    ∃ j : Fin 16, q = p * generatedNinthStandardOctadRepresentative j * p⁻¹ := by
  let r : generatedNinthStandardOctadPointwise := ⟨p⁻¹ * q * p, by
    intro i
    change p.val.symm (q.val (p.val (Fin.castAdd 16 i))) = Fin.castAdd 16 i
    have hi : p.val (Fin.castAdd 16 i) ∈ generatedTenthE7OctadSupport :=
      (hsupport _).mpr i.isLt
    rw [hq _ hi, p.val.symm_apply_apply]⟩
  obtain ⟨j, hj⟩ := generatedTenth_e8_standard_affine_surjective r
  have hr : p⁻¹ * q * p = generatedNinthStandardOctadRepresentative j :=
    (congrArg Subtype.val hj).symm
  refine ⟨j, ?_⟩
  calc
    q = p * (p⁻¹ * q * p) * p⁻¹ := by group
    _ = p * generatedNinthStandardOctadRepresentative j * p⁻¹ := by rw [hr]

/-- Every genuine Golay permutation fixing the actual octad pointwise
is one of the sixteen words. -/
theorem generatedTenth_e8_affine_coverage (q : golayAutomorphismSubgroup)
    (hq : ∀ i ∈ generatedTenthE7OctadSupport, q.val i = i) :
    ∃ j : Fin 16, q = generatedTenthE8AffineRepresentative j := by
  simpa only [generatedTenthE8AffineRepresentative] using
    affine_coverage_of_transport generatedTenthE8StandardPermutation q
      generatedTenth_e8_standard_permutation_support hq

/-- A genuine pointwise-octad permutation preserving the whole norm-twelve support is identity. -/
theorem generatedTenth_e8_affine_line_kernel (q : golayAutomorphismSubgroup)
    (hq : ∀ i ∈ generatedTenthE7OctadSupport, q.val i = i)
    (hs : ∀ i ∈ generatedTenthE7LineSupport, q.val i ∈ generatedTenthE7LineSupport) : q = 1 := by
  obtain ⟨j, rfl⟩ := generatedTenth_e8_affine_coverage q hq
  have hj := (generatedTenth_e8_affine_line_support j).mp hs
  rw [hj, generatedTenth_e8_affine_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
