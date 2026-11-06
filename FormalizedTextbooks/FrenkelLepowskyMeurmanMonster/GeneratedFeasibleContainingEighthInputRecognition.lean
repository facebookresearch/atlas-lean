/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNormalizedShortOrbit

/-! Actual source point stabilizer transport identifies original transition destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Multiplying an original input word by a genuine whole-source fixer preserves its actual
triality destination class under the entire original first-axis action. -/
theorem generatedFeasibleContaining_destination_source_fixer
    (h u : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hu : rhoLocal u.val generatedFeasibleContainingOctadDestination =
      generatedFeasibleContainingOctadDestination) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) (h * u)) =
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination
          (Quotient.mk (QuotientGroup.rightRel
            (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) := by
  change Quotient.mk (MulAction.orbitRel
    (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace)
      (sExtra (rhoLocal (h.val * u.val) generatedFeasibleContainingOctadDestination)) =
        Quotient.mk _ (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination))
  rw [map_mul, LinearEquiv.mul_apply, hu]

/-- A genuine whole-source point stabilizer mover between inverse secondary images identifies
both original transition classes. The mover is an explicit actual group element. -/
theorem generatedFeasibleContaining_destination_inverse_mover
    (h k u : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hu : rhoLocal u.val generatedFeasibleContainingOctadDestination =
      generatedFeasibleContainingOctadDestination)
    (hm : rhoLocal u.val
      (rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) =
        rhoLocal k.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) =
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination
          (Quotient.mk (QuotientGroup.rightRel
            (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) k) := by
  have hi : rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) =
      rhoLocal (k * u).val⁻¹
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
    have hh := congrArg (rhoLocal u.val).symm hm
    rw [LinearEquiv.symm_apply_apply] at hh
    change _ = (rhoLocal u.val).symm (rhoLocal k.val⁻¹ _) at hh
    rw [show (k * u).val⁻¹ = u.val⁻¹ * k.val⁻¹ from by simp,
      map_mul, map_inv]
    simpa only [map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv] using hh
  have hc : Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h =
        Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) (k * u) := by
    apply generatedFeasibleContainingInverseSecondaryCosets.injective
    apply Subtype.ext
    rw [generatedFeasibleContainingInverseSecondaryCosets_apply,
      generatedFeasibleContainingInverseSecondaryCosets_apply]
    exact hi
  rw [hc]
  exact generatedFeasibleContaining_destination_source_fixer k u hu

private theorem octad_matrix_fixed_section (o : Fin 759) (e : Fin 64) (c : ZMod 2)
    (g : leechIsomSubgroup)
    (h : conwayMatrixAction g
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 =
        (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1) :
    generatedAxisE8ImageSection g (golayOctadWord o) =
      generatedAxisE8CoordinateSection (golayOctadWord o) := by
  have hd : Matrix.diagonal (fun i => if golayOctadWord o i = 0 then (0 : ℝ) else 1) =
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 := by
    rw [generatedAxis_triality_octad_matrix]
    apply congrArg (fun f : Fin 24 → ℝ => Matrix.diagonal f)
    funext i
    have hi : golayOctadWord o i ≠ 0 ↔
        (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true := by
      simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
        Finset.mem_univ, true_and] using golayOctadWord_ne_zero_iff o i
    by_cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
    · simp [hb, hi.mpr hb]
    · have hz : golayOctadWord o i = 0 := by
        by_contra hn
        exact hb (hi.mp hn)
      simp [hz, hb]
  rw [← hd, generatedAxisE8_matrix_action_iff_section_stabilizer] at h
  exact h

/-- Every genuine source-section and preferred-first-root fixer lifts to an actual whole-source
axis fixer in the actual signed first-axis group, retaining exactly its original spatial action.
-/
theorem generatedFeasibleContaining_source_flag_whole_lift (g : leechIsomSubgroup)
    (hgS : generatedAxisE8ImageSection g
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex))
    (hgP : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    ∃ f : localFiberSubgroup, f.val.2 = g ∧
      localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair ∧
      rhoLocal (localFiberIntoH f) generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingOctadDestination := by
  obtain ⟨h, hhP, hhS⟩ := generatedFeasibleContaining_source_transport
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH t = h at ht
  rw [← ht] at hhP hhS
  let a := t.val.2
  have haP : griessShortPermutation a (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasibleContainingIncidentPair) := by
    change localGriessRepresentation t
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 at hhP
    rw [generatedAxis_localFiber_image] at hhP
    exact congrArg Prod.fst (@generatedAxis_signed_injective
      (griessShortPermutation a (Sum.inl (0, generatedFeasiblePhysicalRootPair)),
        localShortPhase t (Sum.inl (0, generatedFeasiblePhysicalRootPair)) + 0)
      (Sum.inl (0, generatedFeasibleContainingIncidentPair), 0) hhP)
  let b := a * g * a⁻¹
  have hbM : conwayMatrixAction b (griessConwayEncode (generatedOctadLocalAxis 0 0)).1 =
      (griessConwayEncode (generatedOctadLocalAxis 0 0)).1 := by
    have haM := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hhS
    change (griessConwayEncode (localGriessRepresentation t
      generatedFeasibleContainingOctadDestination)).1 = _ at haM
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at haM
    change conwayMatrixAction a
      (griessConwayEncode generatedFeasibleContainingOctadDestination).1 = _ at haM
    have hgM := generatedAxisE8_octad_stabilizer_axis_matrix
      generatedFeasibleContainingOctadPrototypeIndex 0 0 g hgS
    change conwayMatrixAction g
      (griessConwayEncode generatedFeasibleContainingOctadDestination).1 =
        (griessConwayEncode generatedFeasibleContainingOctadDestination).1 at hgM
    change conwayMatrixAction (a * g * a⁻¹) _ = _
    rw [map_mul, map_mul, map_inv]
    change conwayMatrixAction a (conwayMatrixAction g
      ((conwayMatrixAction a).symm _)) = _
    rw [← haM, LinearEquiv.symm_apply_apply, hgM, haM]
  have hbS := octad_matrix_fixed_section generatedOctadBasisOctad 0 0 b hbM
  have hbP : griessShortPermutation b (Sum.inl (0, generatedFeasibleContainingIncidentPair)) =
      Sum.inl (0, generatedFeasibleContainingIncidentPair) := by
    change griessShortPermutation (a * g * a⁻¹) _ = _
    rw [map_mul, map_mul, map_inv]
    change griessShortPermutation a (griessShortPermutation g
      ((griessShortPermutation a).symm _)) = _
    rw [← haP, Equiv.symm_apply_apply, hgP, haP]
  obtain ⟨v, hvB, hvS⟩ := generatedOctad_projected_stabilizer_lift 0 0 b hbS
  change rhoLocal (localFiberIntoH v) (generatedOctadLocalAxis 0 0) =
    generatedOctadLocalAxis 0 0 at hvS
  have hvP := generatedFeasibleContainingIncident_first_fixed v hvS
    (by rw [hvB]; exact hbP)
  let f := t⁻¹ * v * t
  refine ⟨f, ?_, ?_, ?_⟩
  · change a⁻¹ * v.val.2 * a = g
    rw [hvB]
    dsimp only [b]
    group
  · change rhoLocal (localFiberIntoH (t⁻¹ * v * t))
      (conwayAxis generatedFeasiblePhysicalRootPair) =
        conwayAxis generatedFeasiblePhysicalRootPair
    rw [← conwayShortAxis_pair_zero]
    have hvFirst : rhoLocal (localFiberIntoH v)
        (conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0) =
          conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact hvP
    change rhoLocal ((localFiberIntoH t)⁻¹ * localFiberIntoH v * localFiberIntoH t) _ = _
    rw [map_mul, map_mul, map_inv]
    change (rhoLocal (localFiberIntoH t)).symm
      (rhoLocal (localFiberIntoH v) (rhoLocal (localFiberIntoH t) _)) = _
    rw [hhP, hvFirst, ← hhP, LinearEquiv.symm_apply_apply]
  · change rhoLocal ((localFiberIntoH t)⁻¹ * localFiberIntoH v * localFiberIntoH t) _ = _
    rw [map_mul, map_mul, map_inv]
    change (rhoLocal (localFiberIntoH t)).symm
      (rhoLocal (localFiberIntoH v) (rhoLocal (localFiberIntoH t) _)) = _
    rw [hhS, hvS, ← hhS, LinearEquiv.symm_apply_apply]

private theorem doubled_projection_embedding (u : leechIntegral) :
    leechCoordinateEmbedding (generatedFeasibleContainingDoubledProjection u).val =
      (2 : ℝ) • (Matrix.diagonal (fun i : Fin 24 =>
        if golayStandardOctad i = 0 then (0 : ℝ) else 1) *ᵥ leechCoordinateEmbedding u.val) := by
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  change (((generatedFeasibleContainingDoubledProjection u).val i : ℝ) / Real.sqrt 8) =
    2 * ((if golayStandardOctad i = 0 then (0 : ℝ) else 1) *
      ((u.val i : ℝ) / Real.sqrt 8))
  rw [generatedFeasibleContainingDoubledProjection_coordinate]
  by_cases hi : i.val < 8
  · simp only [golayStandardOctad, hi, ite_true, Pi.smul_apply, smul_eq_mul,
      one_ne_zero, ite_false, one_mul, leechCoordinateEmbedding]
    push_cast
    ring
  · simp [golayStandardOctad, hi, leechCoordinateEmbedding]

/-- Genuine source-section preservation makes the actual doubled integral projection commute
with the entire original lattice isometry. -/
theorem generatedFeasibleContaining_doubled_projection_commutes (g : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)) (u : leechIntegral) :
    generatedFeasibleContainingDoubledProjection (leechIntegralAction g u) =
      leechIntegralAction g (generatedFeasibleContainingDoubledProjection u) := by
  rw [generatedFeasibleContaining_selected_source_word] at hg
  have hc := generatedAxisE8_preserving_projection_commute golayStandardOctad g
    (generatedAxisE8_preserves_of_image_eq _ _ hg)
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [doubled_projection_embedding, leechIntegralAction_embedding,
    leechIntegralAction_embedding, doubled_projection_embedding, map_smul]
  have h := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ =>
    A *ᵥ leechCoordinateEmbedding u.val) hc
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
  rw [leechIsomMatrix_mulVec, leechIsomMatrix_mulVec] at h
  exact congrArg (fun v : Fin 24 → ℝ => (2 : ℝ) • v) h.symm

/-- The entire original source-preserving action preserves the actual selected integral square.
-/
theorem generatedFeasibleContaining_selected_square_preserved (g : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)) (u : leechIntegral) :
    generatedFeasibleContainingSelectedSquare
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
        (leechIntegralAction g u).val =
      generatedFeasibleContainingSelectedSquare
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) u.val := by
  have h := generatedFeasibleContainingDoubledProjection_square (leechIntegralAction g u)
  rw [generatedFeasibleContaining_doubled_projection_commutes g hg u,
    leechIntegralAction_squareSum, generatedFeasibleContainingDoubledProjection_square] at h
  omega

/-- Preferred labels retain their actual selected square under every genuine source-section
isometry, including the actual physical orientation change. -/
theorem generatedFeasibleContaining_selected_short_square_preserved (g : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)) (r : GriessShortIndex) :
    generatedFeasibleContainingSelectedShortSquare (griessShortPermutation g r) =
      generatedFeasibleContainingSelectedShortSquare r := by
  have h := generatedFeasibleContaining_selected_square_preserved g hg (griessShortLatticeVector r)
  rcases generatedE8Short_integral_sign g r with hs | hs
  · rw [hs] at h
    exact h
  · rw [hs] at h
    simpa only [generatedFeasibleContainingSelectedShortSquare,
      generatedFeasibleContainingSelectedSquare, griessShortLatticeVector, Submodule.coe_neg,
      Pi.neg_apply, neg_sq] using h

private theorem doubled_projection_neg (u : leechIntegral) :
    generatedFeasibleContainingDoubledProjection (-u) =
      -generatedFeasibleContainingDoubledProjection u := by
  unfold generatedFeasibleContainingDoubledProjection
  rw [map_neg]
  abel

private theorem coordinate_two_octad (r : GriessShortIndex)
    (h : (griessShortIntegral r 0) ^ 2 = 4) :
    ∃ z : Fin 759 × Fin 64, r = Sum.inr (Sum.inl z) := by
  rcases r with z | z
  · rcases z with ⟨s, p⟩
    change (4 * (if (0 : Fin 24) = (griessCoordinatePair p).1 then (1 : ℤ) else 0) +
      (if s = 0 then -4 else 4) *
        (if (0 : Fin 24) = (griessCoordinatePair p).2 then 1 else 0)) ^ 2 = 4 at h
    split_ifs at h <;> norm_num at h
  · rcases z with z | z
    · exact ⟨z, rfl⟩
    · rcases z with ⟨d, j⟩
      change ((if (golayEncodedMask d.val).testBit 0 then (-1 : ℤ) else 1) *
        (if (0 : Fin 24) = j then -3 else 1)) ^ 2 = 4 at h
      split_ifs at h <;> norm_num at h

private theorem normalized_mem (r : GriessShortIndex)
    (hS : generatedFeasibleContainingSelectedShortSquare r = 8)
    (hP : griessShortIntegral r 0 = griessShortIntegral r 1)
    (h0 : (griessShortIntegral r 0)^2 = 4) :
    r ∈ generatedFeasibleContainingNormalizedShortLabels := by
  obtain ⟨⟨o, e⟩, hr⟩ := coordinate_two_octad r h0
  have ho : o ∈ generatedFeasibleOctadContainingLabels := by
    have h1 : (griessShortIntegral r 1)^2 = 4 := by rw [← hP]; exact h0
    rw [hr] at h0 h1
    have hb0 : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = true := by
      by_contra hn
      have hb : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = false := by
        cases h : (golayEncodedMask (golayOctadLabel o).val).testBit 0 <;> simp_all
      simp only [griessShortIntegral, Fin.val_zero, hb, Bool.false_eq_true, ite_false] at h0
      norm_num at h0
    have hb1 : (golayEncodedMask (golayOctadLabel o).val).testBit 1 = true := by
      by_contra hn
      have hb : (golayEncodedMask (golayOctadLabel o).val).testBit 1 = false := by
        cases h : (golayEncodedMask (golayOctadLabel o).val).testBit 1 <;> simp_all
      simp only [griessShortIntegral, Fin.val_one, hb, Bool.false_eq_true, ite_false] at h1
      norm_num at h1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0, hb1⟩
  have hw : generatedFeasibleContainingOctadSelectedWeight o = 2 := by
    rw [hr, generatedFeasibleContainingSelectedShortSquare_octad_weight] at hS
    omega
  apply Finset.mem_map.mpr
  refine ⟨(o, e), ?_, hr.symm⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
  · exact Finset.mem_filter.mpr ⟨ho, hw⟩
  · exact hr ▸ hP

private theorem mate_coordinate (i : Fin 24) :
    griessShortIntegral generatedFeasibleMateLabel i =
      4 * (if i = 0 ∨ i = 1 then 1 else 0) := by
  change (4 * (if i = (griessCoordinatePair generatedFeasiblePhysicalRootPair).1 then
      (1 : ℤ) else 0) + 4 *
        (if i = (griessCoordinatePair generatedFeasiblePhysicalRootPair).2 then 1 else 0)) = _
  rw [generatedFeasiblePhysicalRootPair_coordinates]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [h0, h1]

private theorem mate_projection_line :
    ∃ m : generatedFeasibleContainingE7ProjectionRootLines,
      m.val.val = generatedFeasibleMateLabel := by
  have hm : griessShortLatticeVector generatedFeasibleMateLabel ∈
      generatedAxisE8CoordinateSection golayStandardOctad := by
    intro i hi
    have hn : ¬ i.val < 8 := by intro h; simp [golayStandardOctad, h] at hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hn
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hn
    change griessShortIntegral generatedFeasibleMateLabel i = 0
    simp only [generatedFeasibleMateLabel, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates, h0, h1, ite_false, mul_zero, add_zero]
  refine ⟨⟨⟨generatedFeasibleMateLabel, hm⟩, ?_⟩, rfl⟩
  simp [generatedFeasibleMateLabel, griessShortIntegral,
    generatedFeasiblePhysicalRootPair_coordinates]

/-- Every original selected-square-eight perpendicular short vector has a genuine source-section
and positive-first-root normalization to the complete original512-label catalogue. -/
theorem generatedFeasibleContaining_selected_eight_spatial_normalize (r : GriessShortIndex)
    (hS : generatedFeasibleContainingSelectedShortSquare r = 8)
    (hP : griessShortIntegral r 0 = griessShortIntegral r 1) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
          generatedAxisE8CoordinateSection
            (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
      leechIntegralAction g
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
      griessShortPermutation g r ∈ generatedFeasibleContainingNormalizedShortLabels := by
  obtain ⟨s, hs⟩ := generatedFeasibleContaining_selected_eight_projected_line r hS hP
  obtain ⟨m, hm⟩ := mate_projection_line
  obtain ⟨g, hgS, hgP, hgM⟩ := generatedFeasibleContainingE7_projection_lines_transitive s m
  rw [hm] at hgM
  have hgS' : generatedAxisE8ImageSection g
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) := by
    rwa [generatedFeasibleContaining_selected_source_word]
  refine ⟨g, hgS', hgP, ?_⟩
  have hS' : generatedFeasibleContainingSelectedShortSquare (griessShortPermutation g r) = 8 := by
    rw [generatedFeasibleContaining_selected_short_square_preserved g hgS', hS]
  have hproj : generatedFeasibleContainingDoubledProjection
      (griessShortLatticeVector (griessShortPermutation g r)) =
        griessShortLatticeVector generatedFeasibleMateLabel ∨
      generatedFeasibleContainingDoubledProjection
        (griessShortLatticeVector (griessShortPermutation g r)) =
          -griessShortLatticeVector generatedFeasibleMateLabel := by
    have hc := generatedFeasibleContaining_doubled_projection_commutes g hgS'
      (griessShortLatticeVector r)
    have hsM := generatedE8Short_integral_sign g s.val.val
    rw [hgM] at hsM
    rcases generatedE8Short_integral_sign g r with ho | ho <;>
      rcases hs with hs | hs <;> rcases hsM with hm | hm
    all_goals
      rw [ho, hs] at hc
      simp only [doubled_projection_neg, map_neg, hm, neg_neg] at hc
      first
      | exact Or.inl hc
      | exact Or.inr hc
      | have hn := congrArg (fun u : leechIntegral => -u) hc
        simp only [neg_neg] at hn
        exact Or.inl hn
      | have hn := congrArg (fun u : leechIntegral => -u) hc
        simp only [neg_neg] at hn
        exact Or.inr hn
  have hc (i : Fin 24) (hi : i.val < 8) :
      griessShortIntegral (griessShortPermutation g r) i =
        (if i = 0 ∨ i = 1 then 2 else 0) ∨
      griessShortIntegral (griessShortPermutation g r) i =
        -(if i = 0 ∨ i = 1 then 2 else 0) := by
    rcases hproj with h | h
    · have hh := congrArg (fun u : leechIntegral => u.val i) h
      rw [generatedFeasibleContainingDoubledProjection_coordinate, ite_eq_left hi] at hh
      change 2 * griessShortIntegral (griessShortPermutation g r) i =
        griessShortIntegral generatedFeasibleMateLabel i at hh
      rw [mate_coordinate] at hh
      by_cases hn : i = 0 ∨ i = 1
      · rw [ite_eq_left hn] at hh ⊢
        omega
      · rw [ite_eq_right hn] at hh ⊢
        omega
    · have hh := congrArg (fun u : leechIntegral => u.val i) h
      rw [generatedFeasibleContainingDoubledProjection_coordinate, ite_eq_left hi] at hh
      change 2 * griessShortIntegral (griessShortPermutation g r) i =
        -griessShortIntegral generatedFeasibleMateLabel i at hh
      rw [mate_coordinate] at hh
      by_cases hn : i = 0 ∨ i = 1
      · rw [ite_eq_left hn] at hh ⊢
        omega
      · rw [ite_eq_right hn] at hh ⊢
        omega
  have h0 := hc 0 (by decide)
  norm_num at h0
  apply normalized_mem _ hS'
  · rcases hproj with hp | hp
    all_goals
      have hh := congrArg (fun u : leechIntegral => u.val 0 - u.val 1) hp
      rw [generatedFeasibleContainingDoubledProjection_coordinate,
        generatedFeasibleContainingDoubledProjection_coordinate] at hh
      first
      | change 2 * griessShortIntegral (griessShortPermutation g r) 0 -
          2 * griessShortIntegral (griessShortPermutation g r) 1 =
            griessShortIntegral generatedFeasibleMateLabel 0 -
              griessShortIntegral generatedFeasibleMateLabel 1 at hh
      | change 2 * griessShortIntegral (griessShortPermutation g r) 0 -
          2 * griessShortIntegral (griessShortPermutation g r) 1 =
            -griessShortIntegral generatedFeasibleMateLabel 0 -
              -griessShortIntegral generatedFeasibleMateLabel 1 at hh
      rw [mate_coordinate, mate_coordinate] at hh
      norm_num at hh
      omega
  · rcases h0 with h0 | h0 <;> rw [h0] <;> norm_num

private theorem pointwise_supported_fixed (g : generatedFeasibleContainingSourcePointwiseSpatial)
    (u : leechIntegral) (hu : generatedOctadSupported golayStandardOctad u.val) :
    leechIntegralAction g.val u = u := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  have hx := pi_eq_sum_univ' (leechCoordinateEmbedding u.val)
  rw [hx, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  by_cases hi : i.val < 8
  · rw [(generatedFeasibleContainingSourcePointwiseSpatial_mem g.val).mp g.property i hi]
  · have hu0 := hu i (by simp [golayStandardOctad, hi])
    change ((u.val i : ℝ) / Real.sqrt 8) • g.val.val (Pi.single i 1) =
      ((u.val i : ℝ) / Real.sqrt 8) • (Pi.single i 1)
    rw [hu0]
    simp only [Int.cast_zero, zero_div, zero_smul]

private theorem pointwise_source_flag (g : generatedFeasibleContainingSourcePointwiseSpatial) :
    generatedAxisE8ImageSection g.val
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
    griessShortPermutation g.val (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair) := by
  have hgS : generatedOctadPreserves golayStandardOctad g.val := by
    intro u
    constructor
    · intro hu
      have h := pointwise_supported_fixed g⁻¹ (leechIntegralAction g.val u) hu
      change leechIntegralAction g.val⁻¹ (leechIntegralAction g.val u) =
        leechIntegralAction g.val u at h
      rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h
      rwa [← h] at hu
    · intro hu
      rw [pointwise_supported_fixed g u hu]
      exact hu
  constructor
  · rw [generatedFeasibleContaining_selected_source_word]
    exact generatedAxisE8_preserving_image _ _ hgS
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    have hu : generatedOctadSupported golayStandardOctad
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))).val := by
      intro i hi
      have hn : ¬ i.val < 8 := by intro h; simp [golayStandardOctad, h] at hi
      have h0 : i ≠ 0 := by intro h; subst i; norm_num at hn
      have h1 : i ≠ 1 := by intro h; subst i; norm_num at hn
      simp only [griessShortLatticeVector, griessShortIntegral,
        generatedFeasiblePhysicalRootPair_coordinates, h0, h1, ite_false,
        mul_zero, add_zero]
    exact pointwise_supported_fixed g _ hu

/-- Every actual signed selected-eight perpendicular short axis is transported to either phase
of the original2306 anchor by a genuine whole-source fixer in the entire original first-axis group.
-/
theorem generatedFeasibleContaining_selected_eight_signed_transport
    (r : GriessShortIndex) (c d : ZMod 2)
    (hS : generatedFeasibleContainingSelectedShortSquare r = 8)
    (hP : griessShortIntegral r 0 = griessShortIntegral r 1) :
    ∃ u : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      rhoLocal u.val generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingOctadDestination ∧
      rhoLocal u.val (conwayShortAxis r c) =
        conwayShortAxis generatedFeasibleContainingNormalizedShortLabel d := by
  obtain ⟨g, hgS, hgP, hgR⟩ :=
    generatedFeasibleContaining_selected_eight_spatial_normalize r hS hP
  have hgP' : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair) :=
    (leechRootedA2_short_perm_eq_iff _ _ _).mpr (Or.inl hgP)
  obtain ⟨f₁, hf₁, hfirst₁, hsource₁⟩ :=
    generatedFeasibleContaining_source_flag_whole_lift g hgS hgP'
  obtain ⟨a, ha⟩ := generatedFeasibleContaining_normalized_short_transitive _ hgR
  have hflag := pointwise_source_flag a
  obtain ⟨f₂, hf₂, hfirst₂, hsource₂⟩ :=
    generatedFeasibleContaining_source_flag_whole_lift a.val hflag.1 hflag.2
  let u : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨localFiberIntoH f₁, hfirst₁⟩
  let v : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨localFiberIntoH f₂, hfirst₂⟩
  let k := v⁻¹ * u
  let f := f₂⁻¹ * f₁
  have hk : localFiberIntoH f = k.val := rfl
  have hkS : rhoLocal k.val generatedFeasibleContainingOctadDestination =
      generatedFeasibleContainingOctadDestination := by
    change rhoLocal ((localFiberIntoH f₂)⁻¹ * localFiberIntoH f₁) _ = _
    rw [map_mul, map_inv]
    change (rhoLocal (localFiberIntoH f₂)).symm
      (rhoLocal (localFiberIntoH f₁) _) = _
    rw [hsource₁]
    apply (rhoLocal (localFiberIntoH f₂)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hsource₂.symm
  have hperm : griessShortPermutation f.val.2 r =
      generatedFeasibleContainingNormalizedShortLabel := by
    change griessShortPermutation (f₂.val.2⁻¹ * f₁.val.2) r = _
    rw [hf₁, hf₂, map_mul, map_inv]
    change (griessShortPermutation a.val).symm (griessShortPermutation g r) = _
    rw [← ha, Equiv.symm_apply_apply]
  let b := localShortPhase f r + c
  have hkR : rhoLocal k.val (conwayShortAxis r c) =
      conwayShortAxis generatedFeasibleContainingNormalizedShortLabel b := by
    rw [← hk]
    change localGriessRepresentation f _ = _
    rw [generatedAxis_localFiber_image, hperm]
  by_cases hb : b = d
  · exact ⟨k, hkS, hb ▸ hkR⟩
  · have hphase : 1 + b = d := by
      have h : ∀ b d : ZMod 2, b ≠ d → 1 + b = d := by decide +kernel
      exact h b d hb
    refine ⟨generatedFeasibleContainingSourcePhaseWord * k, ?_, ?_⟩
    · change rhoLocal (generatedFeasibleContainingSourcePhaseWord.val * k.val) _ = _
      rw [map_mul, LinearEquiv.mul_apply, hkS,
        generatedFeasibleContainingSourcePhaseWord_source]
    · change rhoLocal (generatedFeasibleContainingSourcePhaseWord.val * k.val) _ = _
      rw [map_mul, LinearEquiv.mul_apply, hkR,
        generatedFeasibleContainingSourcePhaseWord_anchor, hphase]

private theorem new_word_positive_first :
    leechIntegralAction generatedFeasibleContainingNewSpatialWord
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
        griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  have hs := generatedE8Short_integral_sign generatedFeasibleContainingNewSpatialWord
    (Sum.inl (0, generatedFeasiblePhysicalRootPair))
  rw [generatedFeasibleContainingNewSpatialWord_first] at hs
  rcases hs with h | h
  · exact h
  · have hp := generatedFeasibleContaining_integral_action_pairing
      generatedFeasibleContainingNewSpatialWord generatedFeasibleContainingNewFrame
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
    rw [generatedFeasibleContainingNewSpatialWord_frame, h,
      generatedFeasibleContainingNewFrame_pairing] at hp
    change (∑ i : Fin 24, (Pi.single (0 : Fin 24) (8 : ℤ) : Fin 24 → ℤ) i *
      -griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i) = 32 at hp
    have he : (∑ i : Fin 24, (Pi.single (0 : Fin 24) (8 : ℤ) : Fin 24 → ℤ) i *
        -griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i) = -32 := by
      rw [Finset.sum_eq_single (0 : Fin 24)]
      · norm_num [Pi.single_apply, griessShortIntegral,
          generatedFeasiblePhysicalRootPair_coordinates]
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · intro hi
        exact False.elim (hi (Finset.mem_univ _))
    rw [he] at hp
    norm_num at hp

private theorem mate_frame_difference :
    griessShortLatticeVector generatedFeasibleMateLabel = leechCoordinateFrameLattice 0 -
      griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  apply Subtype.ext
  funext i
  simp only [griessShortLatticeVector, generatedFeasibleMateLabel, griessShortIntegral,
    generatedFeasiblePhysicalRootPair_coordinates, leechCoordinateFrameLattice,
    leechCoordinateFrameVector, Submodule.coe_sub, Pi.sub_apply]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [h0, h1]

private theorem new_frame_anchor_difference :
    generatedFeasibleContainingNewFrame -
      griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        griessShortLatticeVector generatedFeasibleContainingNormalizedShortLabel := by
  apply Subtype.ext
  funext i
  change generatedFeasibleContainingNewFrameCoordinates i -
    griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i =
      griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i
  rw [generatedFeasibleContaining_normalized_anchor_coordinate]
  simp only [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates]
  have h : ∀ i : Fin 24, generatedFeasibleContainingNewFrameCoordinates i -
      (4 * (if i = 0 then (1 : ℤ) else 0) - 4 * (if i = 1 then 1 else 0)) =
        if (golayEncodedMask 2306).testBit i.val then 2 else 0 := by decide +kernel
  simpa only [neg_mul, sub_eq_add_neg, ite_true] using h i

/-- The original sixth representative has exactly the original2306 preferred inverse-secondary
label, established from its entire actual frame and positive root transport. -/
theorem generatedFeasibleContaining_new_inverse_mate_label :
    griessShortPermutation generatedFeasibleContainingNewSpatialWord⁻¹
      generatedFeasibleMateLabel = generatedFeasibleContainingNormalizedShortLabel := by
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  left
  apply (leechIntegralAction generatedFeasibleContainingNewSpatialWord).injective
  rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  rw [← new_frame_anchor_difference, map_sub,
    generatedFeasibleContainingNewSpatialWord_frame, new_word_positive_first]
  exact mate_frame_difference

/-- The actual original word underlying the faithful sixth-class source. -/
def generatedFeasibleContainingEighthAnchorWord :
    localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  ⟨localFiberIntoH generatedFeasibleContainingNewLocalWord,
    generatedFeasibleContainingNewLocalWord_first_fixed⟩

/-- Its actual inverse coset address retains the same original2306 preferred anchor. -/
theorem generatedFeasibleContainingEighthAnchorWord_inverse_label :
    (generatedFeasibleContainingInverseSecondaryAddresses
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
          generatedFeasibleContainingEighthAnchorWord)).val.1 =
      generatedFeasibleContainingNormalizedShortLabel := by
  rw [generatedFeasibleContaining_inverse_secondary_address_label
    generatedFeasibleContainingEighthAnchorWord generatedFeasibleContainingNewLocalWord rfl,
    generatedFeasibleContainingNewLocalWord_spatial,
    generatedFeasibleContaining_new_inverse_mate_label]

/-- The same original anchor word has precisely the independently defined actual sixth destination.
-/
theorem generatedFeasibleContainingEighthAnchorWord_destination :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
            generatedFeasibleContainingEighthAnchorWord) =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination := rfl

/-- Every original selected-eight inverse coset address has the faithful actual sixth destination.
The proof constructs a whole-source mover and then uses the genuine original A/N coset action.
-/
theorem generatedFeasibleContaining_eighth_word_recognition
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hS : generatedFeasibleContainingSelectedShortSquare
      (generatedFeasibleContainingInverseSecondaryAddresses
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 = 8) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination := by
  let a := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
  let k := generatedFeasibleContainingEighthAnchorWord
  let b := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) k)
  have hP : griessShortIntegral a.val.1 0 = griessShortIntegral a.val.1 1 := by
    have hm := a.property
    change a.val ∈ generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ at hm
    rw [Finset.mem_product] at hm
    exact (generatedFeasibleOrthogonalShortLabels_mem a.val.1).mp hm.1
  obtain ⟨u, huS, huR⟩ := generatedFeasibleContaining_selected_eight_signed_transport
    a.val.1 a.val.2 b.val.2 hS hP
  have hb : b.val.1 = generatedFeasibleContainingNormalizedShortLabel :=
    generatedFeasibleContainingEighthAnchorWord_inverse_label
  have hm : rhoLocal u.val
      (rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) =
        rhoLocal k.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
    rw [← generatedFeasibleContainingInverseSecondaryAddresses_axis h,
      ← generatedFeasibleContainingInverseSecondaryAddresses_axis k]
    change rhoLocal u.val (conwayShortAxis a.val.1 a.val.2) =
      conwayShortAxis b.val.1 b.val.2
    rw [hb]
    exact huR
  exact (generatedFeasibleContaining_destination_inverse_mover h k u huS hm).trans
    generatedFeasibleContainingEighthAnchorWord_destination

/-- All64,512 genuine one-eighth inputs from the complete original containing transition have
exactly the independently defined actual sixth destination. No class count is assumed. -/
theorem generatedFeasibleContaining_eighth_input_recognition
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair)
    (hc : c ∈ generatedFeasibleContainingOutgoingCoefficientInputs 1) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination := by
  induction c using Quotient.inductionOn with
  | h h =>
      rw [generatedFeasibleContainingOutgoingCoefficientInputs_word_iff] at hc
      change generatedFeasibleContainingSelectedShortSquare
        (generatedFeasibleContainingInverseSecondaryAddresses
          (Quotient.mk (QuotientGroup.rightRel
            (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 = 8 at hc
      exact generatedFeasibleContaining_eighth_word_recognition h hc

/-- The genuine sixth class receives exactly the whole64,512-input coefficient fiber within the
proved complete noncoordinate containing partition. -/
theorem generatedFeasibleContaining_eighth_noncoordinate_input_iff
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair)
    (hc : c ∈ generatedFeasibleContainingNoncoordinateInputCosets) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c =
        generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination ↔
      c ∈ generatedFeasibleContainingOutgoingCoefficientInputs 1 := by
  constructor
  · intro he
    change c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
      generatedFeasibleContainingInputFirst c = (1 / 8 : ℝ)
    refine ⟨hc, ?_⟩
    change generatedFeasibleContainingAClassFirst
      (generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c) = _
    rw [he]
    exact generatedFeasibleContainingNewDestination_first_coordinate
  · exact generatedFeasibleContaining_eighth_input_recognition c

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
