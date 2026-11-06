/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelectedShortGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingInverseSecondaryCosets

/-! Actual containing frame projections are the selected squares of inverse secondary roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

private theorem selected_linear_combination (c : Fin 24 → ZMod 2)
    (u v : Fin 24 → ℤ) (a b : ℤ) :
    generatedFeasibleContainingSelectedSquare c (fun i => a * u i + b * v i) =
      a ^ 2 * generatedFeasibleContainingSelectedSquare c u +
        b ^ 2 * generatedFeasibleContainingSelectedSquare c v +
          2 * a * b * (∑ i : Fin 24, (c i).val * u i * v i) := by
  unfold generatedFeasibleContainingSelectedSquare
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem source_root_cross (w : Fin 24 → ℤ) (hw : w 0 = w 1) :
    (∑ i : Fin 24,
      ((golayOctadWord generatedFeasibleContainingOctadPrototypeIndex i).val : ℤ) *
        griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i * w i) = 0 := by
  rw [generatedFeasibleContaining_selected_source_word]
  simp only [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates, ite_true,
    mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  norm_num [golayStandardOctad, hw]

private theorem source_root_selected :
    generatedFeasibleContainingSelectedShortSquare
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 32 := by
  rw [generatedFeasibleContainingSelectedShortSquare_pair,
    generatedFeasiblePhysicalRootPair_coordinates]
  norm_num

private theorem signed_root_selected (w : Fin 24 → ℤ) (hw : w 0 = w 1)
    (a b : ℤ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    generatedFeasibleContainingSelectedSquare
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
      (fun i => a * griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i +
        b * w i) =
          32 + generatedFeasibleContainingSelectedSquare
            (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) w := by
  rw [selected_linear_combination, ha, hb, source_root_cross w hw]
  change 1 * generatedFeasibleContainingSelectedShortSquare
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) + 1 * _ + 2 * a * b * 0 = _
  rw [source_root_selected]
  ring

/-- Physical root preservation gives the exact inverse-root selected square, independently
of both genuine physical representative signs. -/
theorem generatedFeasibleContaining_pullback_frame_short_square (g : leechIsomSubgroup)
    (hg : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    generatedFeasibleContainingSelectedSquare
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
      (generatedFeasibleContainingPullbackFrame g).val =
        32 + generatedFeasibleContainingSelectedShortSquare
          (griessShortPermutation g⁻¹ generatedFeasibleMateLabel) := by
  let r : GriessShortIndex := Sum.inl (0, generatedFeasiblePhysicalRootPair)
  let w := griessShortPermutation g⁻¹ generatedFeasibleMateLabel
  have hgi : griessShortPermutation g⁻¹ r = r := by
    rw [map_inv]
    apply (griessShortPermutation g).symm_apply_eq.mpr
    exact hg.symm
  have hw := generatedFeasiblePhysicalRoot_image_orthogonal g⁻¹ hgi
  have hframe : leechCoordinateFrameLattice 0 =
      griessShortLatticeVector r + griessShortLatticeVector generatedFeasibleMateLabel := by
    have h := generatedFeasibleContaining_pair_frame generatedFeasiblePhysicalRootPair
    rw [generatedFeasiblePhysicalRootPair_coordinates] at h
    exact h.symm
  have hup : generatedFeasibleContainingPullbackFrame g =
      leechIntegralAction g⁻¹ (griessShortLatticeVector r) +
        leechIntegralAction g⁻¹ (griessShortLatticeVector generatedFeasibleMateLabel) := by
    rw [generatedFeasibleContainingPullbackFrame, hframe, map_add]
  rcases generatedE8Short_integral_sign g⁻¹ r with hr | hr <;>
    rcases generatedE8Short_integral_sign g⁻¹ generatedFeasibleMateLabel with hm | hm
  all_goals rw [hgi] at hr; rw [hup, hr, hm]
  · simpa only [Submodule.coe_add, griessShortLatticeVector, Pi.add_def, one_mul,
      generatedFeasibleContainingSelectedShortSquare, r, w] using
      signed_root_selected (griessShortIntegral w) hw 1 1 (by norm_num) (by norm_num)
  · simpa only [Submodule.coe_add, Submodule.coe_neg, Pi.add_def, Pi.neg_def,
      one_mul, neg_one_mul, griessShortLatticeVector,
      generatedFeasibleContainingSelectedShortSquare, r, w] using
      signed_root_selected (griessShortIntegral w) hw 1 (-1) (by norm_num) (by norm_num)
  · simpa only [Submodule.coe_add, Submodule.coe_neg, Pi.add_def, Pi.neg_def,
      one_mul, neg_one_mul, griessShortLatticeVector,
      generatedFeasibleContainingSelectedShortSquare, r, w] using
      signed_root_selected (griessShortIntegral w) hw (-1) 1 (by norm_num) (by norm_num)
  · simpa only [Submodule.coe_add, Submodule.coe_neg, Pi.add_def, Pi.neg_def,
      one_mul, neg_one_mul, griessShortLatticeVector,
      generatedFeasibleContainingSelectedShortSquare, r, w] using
      signed_root_selected (griessShortIntegral w) hw (-1) (-1) (by norm_num) (by norm_num)

/-- The actual inverse-coset preferred label is the genuine inverse spatial image of the mate.
-/
theorem generatedFeasibleContaining_inverse_secondary_address_label
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) (f : localFiberSubgroup)
    (hf : localFiberIntoH f = h.val) :
    (generatedFeasibleContainingInverseSecondaryAddresses
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 =
      griessShortPermutation f.val.2⁻¹ generatedFeasibleMateLabel := by
  let a := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
  have ha := generatedFeasibleContainingInverseSecondaryAddresses_axis h
  have hfi : localFiberIntoH f⁻¹ = h.val⁻¹ := by rw [map_inv, hf]
  rw [← hfi] at ha
  change conwayShortAxis a.val.1 a.val.2 =
    localGriessRepresentation f⁻¹ (generatedFeasibleSecondaryAxis _) at ha
  rw [generatedFeasibleSecondaryAxis_eq_short, generatedAxis_localFiber_image] at ha
  have he := @generatedAxis_signed_injective a.val
    (griessShortPermutation f⁻¹.val.2 generatedFeasibleMateLabel,
      localShortPhase f⁻¹ generatedFeasibleMateLabel + 1) ha
  exact congrArg Prod.fst he

/-- The original word's first matrix diagonal is bound to its exact inverse coset label.
-/
theorem generatedFeasibleContaining_whole_word_diagonal
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) :
    64 * (griessConwayEncode
      (rhoLocal h.val generatedFeasibleContainingOctadDestination)).1 0 0 =
        32 + (generatedFeasibleContainingSelectedShortSquare
          (generatedFeasibleContainingInverseSecondaryAddresses
            (Quotient.mk (QuotientGroup.rightRel
              (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 :
                ℝ) := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair := by
    rw [hf]
    exact h.property
  have hp := ((localAxisStabilizer_mk_iff _ _).mp hfix).1
  have hframe := generatedFeasibleContaining_pullback_frame_short_square f.val.2 hp
  have hlabel := generatedFeasibleContaining_inverse_secondary_address_label h f hf
  rw [← hlabel] at hframe
  have hm := generatedFeasibleContaining_projection_frame_diagonal f.val.2
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
  rw [hframe] at hm
  rw [← hf]
  change 64 * (griessConwayEncode
    (localGriessRepresentation f generatedFeasibleContainingOctadDestination)).1 0 0 = _
  rw [generatedFeasibleContaining_full_fiber_matrix]
  simpa only [Int.cast_add, Int.cast_ofNat] using hm

private theorem selected_of_supported (c : Fin 24 → ZMod 2) (u : Fin 24 → ℤ)
    (hu : generatedOctadSupported c u) :
    generatedFeasibleContainingSelectedSquare c u = leechSquareSum u := by
  unfold generatedFeasibleContainingSelectedSquare leechSquareSum
  apply Finset.sum_congr rfl
  intro i _
  have hb : (c i).val = 0 ∨ (c i).val = 1 := by have h := ZMod.val_lt (c i); omega
  rcases hb with hb | hb
  · have hz := hu i ((ZMod.val_eq_zero _).mp hb)
    simp [hb, hz]
  · simp [hb]

/-- A nonzero actual mate forces the original coordinate frame into the actual image section,
and hence its first matrix diagonal is one. -/
theorem generatedFeasibleContaining_mate_nonzero_diagonal_one (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination)
    (hm : (griessConwayEncode x).2.1 generatedFeasibleMateLabel ≠ 0) :
    (griessConwayEncode x).1 0 0 = 1 := by
  obtain ⟨f, hxf, _⟩ := generatedFeasibleContaining_source_frame_lift x hx
  let S := generatedAxisE8ImageSection f.val.2
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
  have hfirst : griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∈
      S := by
    apply (generatedFeasibleContaining_source_image_short_support f _).mp
    rw [← hxf, generatedFeasibleContaining_first_coordinate x hx]
    norm_num
  have hmate : griessShortLatticeVector generatedFeasibleMateLabel ∈ S := by
    apply (generatedFeasibleContaining_source_image_short_support f _).mp
    rwa [← hxf]
  have hframe := S.add_mem hfirst hmate
  change griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) +
    griessShortLatticeVector (Sum.inl (1, generatedFeasiblePhysicalRootPair)) ∈ S at hframe
  rw [generatedFeasibleContaining_pair_frame,
    generatedFeasiblePhysicalRootPair_coordinates] at hframe
  change leechCoordinateFrameLattice 0 ∈ S at hframe
  obtain ⟨v, hv, hvg⟩ := (generatedAxisE8ImageSection_mem _ _ _).mp hframe
  have he : v = generatedFeasibleContainingPullbackFrame f.val.2 :=
    (leechIntegralAction f.val.2).injective
      (hvg.trans (generatedFeasibleContainingPullbackFrame_image f.val.2).symm)
  rw [he] at hv
  have hs := selected_of_supported
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
    (generatedFeasibleContainingPullbackFrame f.val.2).val hv
  rw [generatedFeasibleContainingPullbackFrame_norm] at hs
  have hp := generatedFeasibleContaining_projection_frame_diagonal f.val.2
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
  rw [hs, ← generatedFeasibleContaining_full_fiber_matrix, ← hxf] at hp
  norm_num at hp
  linarith

/-- Actual mate zero is exactly exclusion of the full selected-short square thirty-two. -/
theorem generatedFeasibleContaining_word_mate_zero_iff
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) :
    (griessConwayEncode (rhoLocal h.val generatedFeasibleContainingOctadDestination)).2.1
      generatedFeasibleMateLabel = 0 ↔
        generatedFeasibleContainingSelectedShortSquare
          (generatedFeasibleContainingInverseSecondaryAddresses
            (Quotient.mk (QuotientGroup.rightRel
              (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 ≠
            32 := by
  let a := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
  have hx : rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination := ⟨h, rfl⟩
  constructor
  · intro hm hs
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
    change localFiberIntoH f = h.val at hf
    have hfix : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair := by
      rw [hf]
      exact h.property
    have hp := ((localAxisStabilizer_mk_iff _ _).mp hfix).1
    have hu := generatedFeasibleContaining_pullback_frame_short_square f.val.2 hp
    have hl := generatedFeasibleContaining_inverse_secondary_address_label h f hf
    rw [← hl, hs] at hu
    norm_num at hu
    have hsup := generatedFeasibleContaining_selected_square_full_supported
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
      (generatedFeasibleContainingPullbackFrame f.val.2)
      (generatedFeasibleContainingPullbackFrame_norm f.val.2) hu
    have hne := generatedFeasibleContaining_frame_full_mate_nonzero f hp hsup
    change (griessConwayEncode
      (rhoLocal (localFiberIntoH f) generatedFeasibleContainingOctadDestination)).2.1 _ ≠ 0 at hne
    rw [hf] at hne
    exact hne hm
  · intro hs
    by_contra hm
    have hd := generatedFeasibleContaining_mate_nonzero_diagonal_one _ hx hm
    have he := generatedFeasibleContaining_whole_word_diagonal h
    rw [hd] at he
    have hh : (generatedFeasibleContainingSelectedShortSquare a.val.1 : ℝ) = 32 := by
      change 64 * 1 = 32 + (generatedFeasibleContainingSelectedShortSquare a.val.1 : ℝ) at he
      linarith
    have hi : generatedFeasibleContainingSelectedShortSquare a.val.1 = 32 := by
      exact_mod_cast hh
    exact hs hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
