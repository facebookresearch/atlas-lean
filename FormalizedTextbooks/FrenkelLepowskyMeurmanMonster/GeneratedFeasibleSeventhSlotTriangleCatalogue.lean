/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatialBound
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhDiagonal
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMiddlePairs
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisTranspositionCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocalCoordinates

/-! Coverage half of the first-axis catalogue for source slot 8 (label 6C1) of Höhn–Seysen,
arXiv:2508.01037, Table 3. Every actual whole-axis fixer of the counted seventh prototype
carries a positive triangle root axis to a positive triangle root axis. The spatial part
preserves the genuine triangle plane support, whose only short vectors are the three
triangle roots up to sign; the actual form value against the prototype then forces the
positive sign. No orbit size or class label is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual final seventh short coefficient on each positive triangle root label is 5/32. -/
theorem generatedFeasibleSeventhSlot_root_coefficient (j : Fin 3) :
    (griessConwayEncode generatedSeventhAxis).2.1 (Sum.inl (0, generatedSeventhTargetPair j)) =
      5 / 32 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hv (i : Fin 24) : generatedNormEightVector generatedSeventhNormEightVector i =
      (generatedSeventhNormEightVectorData 7 i : ℝ) / Real.sqrt 8 := by
    simp only [generatedNormEightVector, generatedSeventhNormEightVector_val,
      leechCoordinateEmbedding]
    rfl
  have hne := griessCoordinatePair_ne (generatedSeventhTargetPair j)
  rw [generatedSeventhAxis_local_expression, generatedFourthQShortBasis_triality_pair_minus,
    generatedSeventh_middle_matrix, generatedSeventh_middle_selected_pair,
    generatedSeventh_middle_pair_coordinate]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hne, ite_false,
    smul_eq_mul, mul_zero, zero_add, generatedNormEightLineMatrix, Matrix.vecMulVec_apply, hv,
    generatedSeventhMiddlePairValue]
  rw [(generatedSeventh_pair_coordinate_certificate j).2]
  fin_cases j <;>
    · simp [generatedSeventhNormEightVectorData]
      field_simp
      nlinarith [hs]

/-- The actual positive pair short vector, with its two physical coordinates. -/
theorem generatedFeasibleSeventhSlot_pair_vector (p : Fin 276) :
    griessShortVector (Sum.inl (0, p)) = fun i => 4 / Real.sqrt 8 *
      ((if i = (griessCoordinatePair p).1 then 1 else 0) -
        (if i = (griessCoordinatePair p).2 then 1 else 0)) := by
  funext i
  simp only [griessShortVector, griessShortIntegral]
  split_ifs <;> push_cast <;> ring

/-- The matrix contraction of a scaled coordinate-difference vector. -/
theorem generatedFeasibleSeventhSlot_contraction_pair (M : Matrix (Fin 24) (Fin 24) ℝ)
    (a b : Fin 24) (κ : ℝ) :
    axisMatrixContraction (fun i => κ * ((if i = a then 1 else 0) - (if i = b then 1 else 0)))
      M = κ ^ 2 * (M a a - M a b - M b a + M b b) := by
  simp only [axisMatrixContraction, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The actual form of each signed triangle root axis against the counted seventh prototype.
It vanishes exactly for the positive sign. -/
theorem generatedFeasibleSeventhSlot_root_form (j : Fin 3) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair j)) c)
      generatedSeventhAxis = 5 / 4 - 5 / 4 * qSign c := by
  have hs : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  rw [griessForm_eq_conwayRawForm, conwayShortAxis_encode, conwayShortAxisRaw_form,
    generatedFeasibleSeventhSlot_root_coefficient, generatedSeventh_axis_matrix,
    generatedFeasibleSeventhSlot_pair_vector, generatedFeasibleSeventhSlot_contraction_pair,
    div_pow, hs]
  rw [(generatedSeventh_pair_coordinate_certificate j).2]
  fin_cases j <;>
    · simp [generatedSeventhAxisMatrix, generatedSeventhMiddlePairValue]
      ring

/-- The three triangle edges, as ordered physical coordinate pairs. -/
def generatedFeasibleSeventhSlotEdge : Fin 3 → Fin 24 × Fin 24 :=
  ![(16, 17), (16, 19), (17, 19)]

/-- The integral coordinate difference along a triangle edge. -/
def generatedFeasibleSeventhSlotEdgeVector (k : Fin 3) (i : Fin 24) : ℤ :=
  (if i = (generatedFeasibleSeventhSlotEdge k).1 then 1 else 0) -
    (if i = (generatedFeasibleSeventhSlotEdge k).2 then 1 else 0)

/-- The integral triangle quadratic: eight times the plane-support value of a short vector. -/
def generatedFeasibleSeventhSlotTriangleQuadratic (u : Fin 24 → ℤ) : ℤ :=
  (u 16 - u 17) ^ 2 + (u 16 - u 19) ^ 2 + (u 17 - u 19) ^ 2

/-- The actual plane-support numerator is the sum of the three edge outer products. -/
theorem generatedFeasibleSeventhSlot_plane_numerator_edges : ∀ i j : Fin 24,
    generatedSeventhPlaneNumerator i j =
      ∑ k : Fin 3, generatedFeasibleSeventhSlotEdgeVector k i *
        generatedFeasibleSeventhSlotEdgeVector k j := by
  decide +kernel

/-- Pairing with an edge vector reads the difference of its two coordinates. -/
theorem generatedFeasibleSeventhSlot_edge_dot (k : Fin 3) (x : Fin 24 → ℝ) :
    (∑ i, (generatedFeasibleSeventhSlotEdgeVector k i : ℝ) * x i) =
      x (generatedFeasibleSeventhSlotEdge k).1 - x (generatedFeasibleSeventhSlotEdge k).2 := by
  simp only [generatedFeasibleSeventhSlotEdgeVector, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The actual plane-support pairing of every short label is its triangle quadratic over eight. -/
theorem generatedFeasibleSeventhSlot_plane_pairing (r : GriessShortIndex) :
    conwayShortPairing generatedSeventhPlaneSupport r =
      (generatedFeasibleSeventhSlotTriangleQuadratic (griessShortIntegral r) : ℝ) / 8 := by
  have hs : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hentry (i j : Fin 24) : generatedSeventhPlaneSupport i j * griessShortVector r i *
      griessShortVector r j = ∑ k : Fin 3,
        ((generatedFeasibleSeventhSlotEdgeVector k i : ℝ) * griessShortVector r i) *
          ((generatedFeasibleSeventhSlotEdgeVector k j : ℝ) * griessShortVector r j) := by
    change (generatedSeventhPlaneNumerator i j : ℝ) * _ * _ = _
    rw [generatedFeasibleSeventhSlot_plane_numerator_edges, Int.cast_sum, Finset.sum_mul,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  have hsum : conwayShortPairing generatedSeventhPlaneSupport r =
      ∑ k : Fin 3, (∑ i, (generatedFeasibleSeventhSlotEdgeVector k i : ℝ) *
        griessShortVector r i) ^ 2 := by
    unfold conwayShortPairing
    simp only [hentry, pow_two, Finset.sum_mul_sum]
    calc
      _ = ∑ i, ∑ k : Fin 3, ∑ j,
          ((generatedFeasibleSeventhSlotEdgeVector k i : ℝ) * griessShortVector r i) *
            ((generatedFeasibleSeventhSlotEdgeVector k j : ℝ) * griessShortVector r j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hsum]
  simp only [generatedFeasibleSeventhSlot_edge_dot, griessShortVector,
    generatedFeasibleSeventhSlotTriangleQuadratic, Fin.sum_univ_three,
    generatedFeasibleSeventhSlotEdge, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  field_simp
  rw [hs]
  ring

/-- Finite pair-shape table: the triangle quadratic of a pair vector is 96 only for the three
positive triangle pairs. -/
theorem generatedFeasibleSeventhSlot_pair_quadratic_table : ∀ a b : Fin 24, ∀ s : Fin 2,
    a < b → generatedFeasibleSeventhSlotTriangleQuadratic (fun i =>
      4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)) =
        96 →
      s = 0 ∧ ((a, b) = (16, 17) ∨ (a, b) = (16, 19) ∨ (a, b) = (17, 19)) := by
  decide +kernel

/-- Only the three positive triangle root labels have triangle quadratic 96. Octad and odd
shapes have too small coordinates, and every other pair shape fails the finite table. -/
theorem generatedFeasibleSeventhSlot_triangle_label (r : GriessShortIndex)
    (h : generatedFeasibleSeventhSlotTriangleQuadratic (griessShortIntegral r) = 96) :
    ∃ k : Fin 3, r = Sum.inl (0, generatedSeventhTargetPair k) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · have hlt : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
      (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
    obtain ⟨hs, hab⟩ := generatedFeasibleSeventhSlot_pair_quadratic_table _ _ s hlt h
    subst hs
    have hk : ∃ k : Fin 3, griessCoordinatePair p = ![(16, 17), (16, 19), (17, 19)] k := by
      rcases hab with hab | hab | hab
      · exact ⟨0, hab⟩
      · exact ⟨1, hab⟩
      · exact ⟨2, hab⟩
    obtain ⟨k, hk⟩ := hk
    refine ⟨k, ?_⟩
    have hp : p = generatedSeventhTargetPair k := by
      apply griessCoordinatePairEquiv.injective
      apply Subtype.ext
      change griessCoordinatePair p = griessCoordinatePair (generatedSeventhTargetPair k)
      rw [hk, (generatedSeventh_pair_coordinate_certificate k).2]
    rw [hp]
  · exfalso
    simp only [generatedFeasibleSeventhSlotTriangleQuadratic, griessShortIntegral] at h
    split_ifs at h <;> norm_num at h
  · exfalso
    simp only [generatedFeasibleSeventhSlotTriangleQuadratic, griessShortIntegral] at h
    split_ifs at h <;> norm_num at h

/-- Each positive triangle root label has triangle quadratic 96. -/
theorem generatedFeasibleSeventhSlot_root_quadratic (j : Fin 3) :
    generatedFeasibleSeventhSlotTriangleQuadratic
      (griessShortIntegral (Sum.inl (0, generatedSeventhTargetPair j))) = 96 := by
  simp only [griessShortIntegral, (generatedSeventh_pair_coordinate_certificate j).2]
  fin_cases j <;> decide +kernel

/-- Every actual spatial isometry fixing the seventh matrix permutes the three positive
triangle root labels. -/
theorem generatedFeasibleSeventhSlot_spatial_label (e : leechIsomSubgroup)
    (he : e ∈ generatedSeventhSpatialStabilizer) (j : Fin 3) :
    ∃ k : Fin 3, griessShortPermutation e (Sum.inl (0, generatedSeventhTargetPair j)) =
      Sum.inl (0, generatedSeventhTargetPair k) := by
  have hP := ((generatedSeventhSpatialStabilizer_mem e).mp he).1
  have hc := conwayShortPairing_covariant e generatedSeventhPlaneSupport
    (Sum.inl (0, generatedSeventhTargetPair j))
  rw [hP, generatedFeasibleSeventhSlot_plane_pairing, generatedFeasibleSeventhSlot_plane_pairing,
    generatedFeasibleSeventhSlot_root_quadratic] at hc
  apply generatedFeasibleSeventhSlot_triangle_label
  have h : (generatedFeasibleSeventhSlotTriangleQuadratic (griessShortIntegral
      (griessShortPermutation e (Sum.inl (0, generatedSeventhTargetPair j)))) : ℝ) = 96 := by
    linarith
  exact_mod_cast h

/-- An actual whole-axis fixer sends each positive triangle root axis to the positive axis on
its permuted label: the form value against the fixed prototype forces phase zero. -/
theorem generatedFeasibleSeventhSlot_fiber_image (f : localFiberSubgroup)
    (hf : localGriessRepresentation f generatedSeventhAxis = generatedSeventhAxis) (j : Fin 3) :
    localGriessRepresentation f (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair j)) 0) =
      conwayShortAxis (griessShortPermutation f.val.2
        (Sum.inl (0, generatedSeventhTargetPair j))) 0 := by
  obtain ⟨k, hk⟩ := generatedFeasibleSeventhSlot_spatial_label f.val.2
    (generatedSeventh_local_fiber_spatial_mem f hf) j
  have hform := localGriessRepresentation_form f
    (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair j)) 0) generatedSeventhAxis
  rw [hf, generatedAxis_localFiber_image, hk, generatedFeasibleSeventhSlot_root_form,
    generatedFeasibleSeventhSlot_root_form, qSign_zero] at hform
  have hq : qSign (localShortPhase f (Sum.inl (0, generatedSeventhTargetPair j)) + 0) = 1 := by
    linarith
  rw [generatedAxis_localFiber_image, (qSign_eq_one_iff _).mp hq]

/-- Coverage: every element of the entire actual seventh H stabilizer carries each positive
triangle root axis to one of the three positive triangle root axes. -/
theorem generatedFeasibleSeventhSlot_coverage (g : H) (hg : g ∈ generatedSeventhLocalAxisStabilizer)
    (j : Fin 3) :
    ∃ k : Fin 3, rhoLocal g (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair j)) 0) =
      conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair k)) 0 := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup g
  change localFiberIntoH f = g at hf
  subst hf
  have hfix : localGriessRepresentation f generatedSeventhAxis = generatedSeventhAxis := hg
  obtain ⟨k, hk⟩ := generatedFeasibleSeventhSlot_spatial_label f.val.2
    (generatedSeventh_local_fiber_spatial_mem f hfix) j
  refine ⟨k, ?_⟩
  change localGriessRepresentation f _ = _
  rw [generatedFeasibleSeventhSlot_fiber_image f hfix j, hk]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
