/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingTransitionResidual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCatalog

/-! Genuine pullback frame coordinates for the original containing-axis projector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Integer square sum of actual frame coordinates selected by an original binary word. -/
def generatedFeasibleContainingSelectedSquare (c : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) : ℤ :=
  ∑ i, ((c i).val : ℤ) * u i ^ 2

/-- Removing the common physical normalization commutes with the actual integral action. -/
theorem generatedFeasibleContaining_integral_action_cast (g : leechIsomSubgroup)
    (u : leechIntegral) :
    (fun i => ((leechIntegralAction g u).val i : ℝ)) =
      g.val (fun i => (u.val i : ℝ)) := by
  have hs (v : leechIntegral) : (Real.sqrt 8 : ℝ) • leechCoordinateEmbedding v.val =
      (fun i => (v.val i : ℝ)) := by
    funext i
    change Real.sqrt 8 * ((v.val i : ℝ) / Real.sqrt 8) = _
    field_simp
  calc
    _ = (Real.sqrt 8 : ℝ) • leechCoordinateEmbedding (leechIntegralAction g u).val :=
      (hs _).symm
    _ = (Real.sqrt 8 : ℝ) • g.val (leechCoordinateEmbedding u.val) := by
      rw [leechIntegralAction_embedding]
    _ = g.val ((Real.sqrt 8 : ℝ) • leechCoordinateEmbedding u.val) := (map_smul _ _ _).symm
    _ = _ := by rw [hs]

/-- The genuine integral action preserves the complete original integer pairing. -/
theorem generatedFeasibleContaining_integral_action_pairing (g : leechIsomSubgroup)
    (u v : leechIntegral) :
    (∑ i : Fin 24, (leechIntegralAction g u).val i * (leechIntegralAction g v).val i) =
      ∑ i : Fin 24, u.val i * v.val i := by
  have h := g.property.1 (fun i => (u.val i : ℝ)) (fun i => (v.val i : ℝ))
  rw [← generatedFeasibleContaining_integral_action_cast,
    ← generatedFeasibleContaining_integral_action_cast] at h
  unfold stdPairingFun at h
  dsimp only at h
  exact_mod_cast h

/-- The actual inverse image of the original norm-eight coordinate frame. -/
def generatedFeasibleContainingPullbackFrame (g : leechIsomSubgroup) : leechIntegral :=
  leechIntegralAction g⁻¹ (leechCoordinateFrameLattice 0)

/-- Its entire original integer norm is exactly sixty-four. -/
theorem generatedFeasibleContainingPullbackFrame_norm (g : leechIsomSubgroup) :
    leechSquareSum (generatedFeasibleContainingPullbackFrame g).val = 64 := by
  rw [generatedFeasibleContainingPullbackFrame, leechIntegralAction_squareSum]
  exact leechCoordinateFrameVector_square 0

/-- Genuine spatial transport takes this actual integral pullback back to the original frame. -/
theorem generatedFeasibleContainingPullbackFrame_image (g : leechIsomSubgroup) :
    leechIntegralAction g (generatedFeasibleContainingPullbackFrame g) =
      leechCoordinateFrameLattice 0 := by
  rw [generatedFeasibleContainingPullbackFrame, ← LinearEquiv.mul_apply, ← map_mul,
    mul_inv_cancel, map_one]
  rfl

/-- The actual root-preserving spatial word gives the exact two possible endpoint differences.
-/
theorem generatedFeasibleContainingPullbackFrame_first_difference (g : leechIsomSubgroup)
    (hg : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    (generatedFeasibleContainingPullbackFrame g).val 0 -
        (generatedFeasibleContainingPullbackFrame g).val 1 = 8 ∨
      (generatedFeasibleContainingPullbackFrame g).val 0 -
        (generatedFeasibleContainingPullbackFrame g).val 1 = -8 := by
  let u := generatedFeasibleContainingPullbackFrame g
  let r := griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))
  have h := generatedFeasibleContaining_integral_action_pairing g u r
  rw [generatedFeasibleContainingPullbackFrame_image] at h
  have hr : ∑ i : Fin 24, u.val i * r.val i = 4 * (u.val 0 - u.val 1) := by
    simp only [r, griessShortLatticeVector, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates]
    simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [hr] at h
  rcases generatedE8Short_integral_sign g
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) with hp | hn
  · rw [hg] at hp
    change leechIntegralAction g r = r at hp
    rw [hp] at h
    norm_num [r, leechCoordinateFrameLattice, leechCoordinateFrameVector,
      griessShortLatticeVector, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates, Pi.single_apply] at h
    left
    linarith
  · rw [hg] at hn
    change leechIntegralAction g r = -r at hn
    rw [hn] at h
    norm_num [r, leechCoordinateFrameLattice, leechCoordinateFrameVector,
      griessShortLatticeVector, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates, Pi.single_apply] at h
    right
    linarith

/-- The genuine inverse real frame is exactly the cast of the actual integral pullback. -/
theorem generatedFeasibleContainingPullbackFrame_cast (g : leechIsomSubgroup) :
    (fun i => ((generatedFeasibleContainingPullbackFrame g).val i : ℝ)) =
      g.val.symm (Pi.single (0 : Fin 24) 8) := by
  have h := generatedFeasibleContaining_integral_action_cast g⁻¹
    (leechCoordinateFrameLattice 0)
  change (fun i => ((generatedFeasibleContainingPullbackFrame g).val i : ℝ)) =
    g.val.symm (fun i => ((leechCoordinateFrameLattice 0).val i : ℝ)) at h
  rw [h]
  congr 1
  funext i
  simp [leechCoordinateFrameLattice, leechCoordinateFrameVector, Pi.single_apply]

private theorem frame_bilinear (M : Matrix (Fin 24) (Fin 24) ℝ) :
    Matrix.toBilin' M (Pi.single (0 : Fin 24) 8) (Pi.single (0 : Fin 24) 8) =
      64 * M 0 0 := by
  have hs : Pi.single (0 : Fin 24) (8 : ℝ) = (8 : ℝ) • Pi.single (0 : Fin 24) 1 := by
    funext i
    simp [Pi.single_apply]
  simp only [hs, map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.toBilin'_single]
  ring

private theorem diagonal_bilinear (w v : Fin 24 → ℝ) :
    Matrix.toBilin' (Matrix.diagonal w) v v = ∑ i : Fin 24, w i * v i ^ 2 := by
  rw [Matrix.toBilin'_apply']
  unfold dotProduct
  simp only [Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual projector diagonal is its genuine integer pullback-frame square sum divided by64.
-/
theorem generatedFeasibleContaining_projection_frame_diagonal (g : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) :
    64 * conwayMatrixAction g (Matrix.diagonal (fun i => ((c i).val : ℝ))) 0 0 =
      (generatedFeasibleContainingSelectedSquare c
        (generatedFeasibleContainingPullbackFrame g).val : ℝ) := by
  have h := conwayMatrixAction_pairing g
    (Matrix.diagonal (fun i => ((c i).val : ℝ)))
    (Pi.single (0 : Fin 24) 8) (Pi.single (0 : Fin 24) 8)
  rw [frame_bilinear, ← generatedFeasibleContainingPullbackFrame_cast,
    diagonal_bilinear] at h
  rw [h]
  simp only [generatedFeasibleContainingSelectedSquare, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, Int.cast_pow]

/-- The original containing projector uses exactly its genuine Golay word's coordinate values.
-/
theorem generatedFeasibleContaining_source_projection_word :
    (griessConwayEncode generatedFeasibleContainingOctadDestination).1 =
      Matrix.diagonal (fun i : Fin 24 =>
        ((golayOctadWord generatedFeasibleContainingOctadPrototypeIndex i).val : ℝ)) := by
  unfold generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadPrototypeLabel
  rw [generatedAxis_triality_octad_matrix]
  congr 1
  funext i
  have h := golayLabelEncoder_match
    (golayOctadLabel generatedFeasibleContainingOctadPrototypeIndex) i
  change (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex i).val = _ at h
  rw [h]
  split_ifs <;> norm_num

/-- Every actual source orbit vector retains an original full fiber and its genuine spatial root.
-/
theorem generatedFeasibleContaining_source_frame_lift (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    ∃ f : localFiberSubgroup,
      x = localGriessRepresentation f generatedFeasibleContainingOctadDestination ∧
      griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) := by
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hx
  change rhoLocal a.val generatedFeasibleContainingOctadDestination = x at ha
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup a.val
  change localFiberIntoH f = a.val at hf
  refine ⟨f, ?_, ?_⟩
  · rw [← ha, ← hf]
    rfl
  · exact ((localAxisStabilizer_mk_iff f generatedFeasiblePhysicalRootPair).mp
      (hf.symm ▸ a.property)).1

/-- The complete genuine source short support is its actual spatial image section. -/
theorem generatedFeasibleContaining_source_image_short_support (f : localFiberSubgroup)
    (r : GriessShortIndex) :
    (griessConwayEncode (localGriessRepresentation f
      generatedFeasibleContainingOctadDestination)).2.1 r ≠ 0 ↔
        r ∈ generatedAxisE8ShortLines (generatedAxisE8ImageSection f.val.2
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)) := by
  obtain ⟨s, hs⟩ := (griessShortPermutation f.val.2).surjective r
  rw [← hs]
  change _ ≠ 0 ↔ griessShortPermutation f.val.2 s ∈ generatedAxisE8ShortLines
    ((generatedAxisE8CoordinateSection
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)).map
        (leechIntegralAction f.val.2).toLinearMap)
  rw [generatedAxisE8ShortLines_image_mem, generatedAxisE8ShortLines_coordinate_mem,
    localGriessRepresentation_encode]
  change localShortOperator f
    (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      (griessShortPermutation f.val.2 s) ≠ 0 ↔ _
  rw [localShortOperator_image, mul_ne_zero_iff]
  have hn : qSign (localShortPhase f s) ≠ 0 := by
    intro hz
    have h := qSign_sq (localShortPhase f s)
    rw [hz] at h
    norm_num at h
  constructor
  · intro hs
    exact (generatedAxis_triality_octad_support_iff _ _ _ _).mp hs.2
  · intro hs
    exact ⟨hn, (generatedAxis_triality_octad_support_iff _ _ _ _).mpr hs⟩

/-- A selected square sum sixty-four puts the entire genuine norm-eight frame in the section. -/
theorem generatedFeasibleContaining_selected_square_full_supported
    (c : Fin 24 → ZMod 2) (u : leechIntegral) (hu : leechSquareSum u.val = 64)
    (hS : generatedFeasibleContainingSelectedSquare c u.val = 64) :
    generatedOctadSupported c u.val := by
  have hn (i : Fin 24) :
      0 ≤ u.val i ^ 2 - ((c i).val : ℤ) * u.val i ^ 2 := by
    have hc : ((c i).val : ℤ) ≤ 1 := by have h := (c i).val_lt; omega
    have h := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (u.val i))
    nlinarith
  have hzero : (∑ i : Fin 24, (u.val i ^ 2 - ((c i).val : ℤ) * u.val i ^ 2)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change leechSquareSum u.val - generatedFeasibleContainingSelectedSquare c u.val = 0
    rw [hu, hS, sub_self]
  intro i hi
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hzero i
    (Finset.mem_univ i)
  rw [hi] at hterm
  norm_num at hterm
  nlinarith

/-- A fully supported actual pullback frame forces the source mate coefficient to be nonzero. -/
theorem generatedFeasibleContaining_frame_full_mate_nonzero (f : localFiberSubgroup)
    (hf : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair))
    (hu : generatedOctadSupported (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
      (generatedFeasibleContainingPullbackFrame f.val.2).val) :
    (griessConwayEncode (localGriessRepresentation f
      generatedFeasibleContainingOctadDestination)).2.1 generatedFeasibleMateLabel ≠ 0 := by
  let S := generatedAxisE8ImageSection f.val.2
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
  have hframe : leechCoordinateFrameLattice 0 ∈ S :=
    (generatedAxisE8ImageSection_mem _ _ _).mpr
      ⟨generatedFeasibleContainingPullbackFrame f.val.2, hu,
        generatedFeasibleContainingPullbackFrame_image _⟩
  have hfirst : Sum.inl (0, generatedFeasiblePhysicalRootPair) ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)) := by
    rw [generatedAxisE8ShortLines_coordinate_mem]
    apply (generatedAxis_triality_octad_support_iff _ _ _ _).mp
    change (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ≠ 0
    rw [generatedFeasibleContaining_source_first_coordinate]
    norm_num
  have hr := (generatedAxisE8ShortLines_image_mem f.val.2 _ _).mpr hfirst
  rw [hf] at hr
  change griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∈ S at hr
  have hmate : griessShortLatticeVector generatedFeasibleMateLabel ∈ S := by
    have hpair := generatedFeasibleContaining_pair_frame generatedFeasiblePhysicalRootPair
    rw [generatedFeasiblePhysicalRootPair_coordinates] at hpair
    have hm : griessShortLatticeVector generatedFeasibleMateLabel =
        leechCoordinateFrameLattice 0 -
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
      rw [← hpair]
      abel
    rw [hm]
    exact S.sub_mem hframe hr
  exact (generatedFeasibleContaining_source_image_short_support f _).mpr hmate

/-- The genuine original source word contains both fixed-root coordinates with value one. -/
theorem generatedFeasibleContaining_source_word_first :
    golayOctadWord generatedFeasibleContainingOctadPrototypeIndex 0 = 1 ∧
      golayOctadWord generatedFeasibleContainingOctadPrototypeIndex 1 = 1 := by
  have hb : ∀ b : ZMod 2, b.val = 1 → b = 1 := by decide +kernel
  constructor
  · apply hb
    unfold golayOctadWord
    rw [golayLabelEncoder_match, generatedFeasibleContainingOctadPrototypeIndex_label]
    decide +kernel
  · apply hb
    unfold golayOctadWord
    rw [golayLabelEncoder_match, generatedFeasibleContainingOctadPrototypeIndex_label]
    decide +kernel

private theorem coordinate_projector_first_fixed (c : Fin 24 → ZMod 2)
    (hc0 : c 0 = 1) (hc1 : c 1 = 1) :
    Matrix.diagonal (fun i : Fin 24 => ((c i).val : ℝ)) *ᵥ
        griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  have hc0v : (c 0).val = 1 := by rw [hc0]; decide
  have hc1v : (c 1).val = 1 := by rw [hc1]; decide
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi0 : i = 0
  · subst i
    rw [hc0v, Nat.cast_one, one_mul]
  · by_cases hi1 : i = 1
    · subst i
      rw [hc1v, Nat.cast_one, one_mul]
    · simp only [griessShortVector, griessShortIntegral,
        generatedFeasiblePhysicalRootPair_coordinates, hi0, hi1, ite_false,
        zero_add, Int.cast_zero, zero_div, mul_zero]

/-- The actual image section projection fixes the complete original first root vector. -/
theorem generatedFeasibleContaining_image_projector_first_fixed (g : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) (hc0 : c 0 = 1) (hc1 : c 1 = 1)
    (hg : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    conwayMatrixAction g (Matrix.diagonal (fun i : Fin 24 => ((c i).val : ℝ))) *ᵥ
        griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  have h := conwayMatrixAction_mulVec g
    (Matrix.diagonal (fun i : Fin 24 => ((c i).val : ℝ)))
    (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
  rw [coordinate_projector_first_fixed c hc0 hc1] at h
  rcases griessShortPermutation_vector g
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) with hp | hn
  · rw [hg] at hp
    rwa [hp] at h
  · rw [hg] at hn
    rw [hn, Matrix.mulVec_neg] at h
    exact neg_injective h

/-- Every full containing fiber retains the actual source Golay projector and spatial image. -/
theorem generatedFeasibleContaining_full_fiber_matrix (f : localFiberSubgroup) :
    (griessConwayEncode (localGriessRepresentation f
      generatedFeasibleContainingOctadDestination)).1 =
        conwayMatrixAction f.val.2 (Matrix.diagonal (fun i : Fin 24 =>
          ((golayOctadWord generatedFeasibleContainingOctadPrototypeIndex i).val : ℝ))) := by
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
    generatedFeasibleContaining_source_projection_word]

/-- Actual fixed-root incidence gives the exact relation between the source diagonal and pair entry.
-/
theorem generatedFeasibleContaining_first_diagonal_relation (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    (griessConwayEncode x).1 0 0 - (griessConwayEncode x).1 0 1 = 1 := by
  obtain ⟨f, hxf, hf⟩ := generatedFeasibleContaining_source_frame_lift x hx
  have h := generatedFeasibleContaining_image_projector_first_fixed f.val.2
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
    generatedFeasibleContaining_source_word_first.1
    generatedFeasibleContaining_source_word_first.2 hf
  rw [← generatedFeasibleContaining_full_fiber_matrix, ← hxf] at h
  have he := congrFun h 0
  simp only [Matrix.mulVec, dotProduct, griessShortVector, griessShortIntegral,
    generatedFeasiblePhysicalRootPair_coordinates] at he
  push_cast at he
  simp only [add_div, mul_add, mul_div, mul_ite, mul_zero, ite_div, zero_div,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  have hn : Real.sqrt 8 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hn] at he
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
