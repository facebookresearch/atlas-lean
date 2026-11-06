/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthExplicitProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Pairing

/-! The actual explicit one-eighth destination recognizes its distinguished mate line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- A genuine phase-correct lift of the certified positive first-root spatial transport exists. -/
theorem generatedFeasibleEighthExplicitLift_exists :
    ∃ f : localFiberSubgroup, f.val.2 = generatedFeasibleEighthExplicitSpatialWord ∧
      localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair := by
  let g := generatedFeasibleEighthExplicitSpatialWord
  have hg : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair) :=
    (leechRootedA2_short_perm_eq_iff _ _ _).mpr
      (Or.inl generatedFeasibleEighthExplicitSpatialWord_first)
  let a := qBinaryIsometryLift (leechBinaryAction g) (leechBinaryAction_squareQuad g)
  obtain ⟨s, hs⟩ := exists_spinHolomorph_lift a
    (qBinaryIsometryLift_central (leechBinaryAction g) (leechBinaryAction_squareQuad g))
  have hf : (s, g) ∈ localFiberSubgroup := by
    change qBinaryAction (spinConjugation s) = leechBinaryAction g
    rw [hs]
    exact qBinaryAction_isometryLift (leechBinaryAction g) (leechBinaryAction_squareQuad g)
  let f : localFiberSubgroup := ⟨(s, g), hf⟩
  obtain ⟨q, hq⟩ := localAxisQPhase_surjective
    (Sum.inl (0, generatedFeasiblePhysicalRootPair))
    (ofAdd (localShortPhase f (Sum.inl (0, generatedFeasiblePhysicalRootPair))))
  let f' := localFiberIncl q * f
  have hp : f'.val.2 = g := by change 1 * g = g; exact one_mul g
  refine ⟨f', hp, (localAxisStabilizer_mk_iff _ _).mpr ⟨?_, ?_⟩⟩
  · rw [hp]
    exact hg
  · rw [localShortPhase_mul]
    rw [show f.val.2 = g from rfl, hg, localAxisQPhase_eq_short_phase, hq]
    exact ZModModule.add_self _

/-- The chosen fiber retains the proved spatial action and first phase. -/
def generatedFeasibleEighthExplicitLocalWord : localFiberSubgroup :=
  Classical.choose generatedFeasibleEighthExplicitLift_exists

theorem generatedFeasibleEighthExplicitLocalWord_spatial :
    generatedFeasibleEighthExplicitLocalWord.val.2 = generatedFeasibleEighthExplicitSpatialWord :=
  (Classical.choose_spec generatedFeasibleEighthExplicitLift_exists).1

theorem generatedFeasibleEighthExplicitLocalWord_first :
    localFiberIntoH generatedFeasibleEighthExplicitLocalWord ∈
      localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  (Classical.choose_spec generatedFeasibleEighthExplicitLift_exists).2

/-- The whole containing axis after the actual phase-correct local frame word. -/
def generatedFeasibleEighthExplicitIncoming : GriessSpace :=
  rhoLocal (localFiberIntoH generatedFeasibleEighthExplicitLocalWord)
    generatedFeasibleContainingOctadDestination

/-- The actual one-eighth feasible axis obtained by triality from the explicit incoming axis. -/
def generatedFeasibleEighthExplicitDestination : GriessSpace :=
  sExtra generatedFeasibleEighthExplicitIncoming

/-- Every original matrix entry of the phase-correct full local word has the proved projection.
-/
theorem generatedFeasibleEighthExplicitIncoming_matrix (i j : Fin 24) :
    (griessConwayEncode generatedFeasibleEighthExplicitIncoming).1 i j =
      (generatedFeasibleEighthExplicitProjectionNumerator i j : ℝ) / 16 := by
  have hm := generatedFeasibleContaining_full_fiber_matrix
    generatedFeasibleEighthExplicitLocalWord
  rw [generatedFeasibleEighthExplicitLocalWord_spatial] at hm
  simp only [golayOctadWord, generatedFeasibleContainingOctadPrototypeIndex_label] at hm
  have hc : ∀ k : Fin 24, ((golayEncoder (golayLabelCoefficients 2063) k).val : ℤ) =
      if (golayEncodedMask 2063).testBit k.val then 1 else 0 := by decide +kernel
  have hd : (fun k : Fin 24 =>
      ((golayEncoder (golayLabelCoefficients 2063) k).val : ℝ)) =
      fun k => if (golayEncodedMask 2063).testBit k.val then (1 : ℝ) else 0 := by
    funext k
    exact_mod_cast hc k
  rw [hd] at hm
  change (griessConwayEncode generatedFeasibleEighthExplicitIncoming).1 = _ at hm
  rw [hm]
  exact generatedFeasibleEighthExplicitProjectionNumerator_actual i j

/-- A nonzero coordinate of a whole spatial image of the original E8 axis pairs by four.
This implication is independent of the chosen spin lift. -/
theorem generatedFeasibleContaining_source_nonzero_pairing (f : localFiberSubgroup)
    (r : GriessShortIndex)
    (hr : (griessConwayEncode (localGriessRepresentation f
      generatedFeasibleContainingOctadDestination)).2.1 r ≠ 0) :
    conwayShortPairing (griessConwayEncode (localGriessRepresentation f
      generatedFeasibleContainingOctadDestination)).1 r = 4 := by
  let t := (griessShortPermutation f.val.2).symm r
  have ht : griessShortPermutation f.val.2 t = r := Equiv.apply_symm_apply _ _
  have hi := localShortOperator_image f
    (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 t
  rw [ht] at hi
  have hc : (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 t ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hi
    apply hr
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    exact hi
  have hs : generatedOctadShortSupport generatedFeasibleContainingOctadPrototypeIndex t := by
    exact (generatedAxis_triality_octad_support_iff _ 0 0 t).mp hc
  have hp := generatedAxisE8_supported_pairing_four
    generatedFeasibleContainingOctadPrototypeIndex 0 0 t hs
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  rw [← ht, conwayShortPairing_covariant]
  exact hp

/-- The physical plus-pair evaluates an arbitrary original matrix in its four entries. -/
theorem generatedFeasibleContaining_plus_pairing (P : Matrix (Fin 24) (Fin 24) ℝ)
    (p : Fin 276) :
    conwayShortPairing P (Sum.inl (1, p)) =
      2 * (P (griessCoordinatePair p).1 (griessCoordinatePair p).1 +
        P (griessCoordinatePair p).2 (griessCoordinatePair p).2 +
        P (griessCoordinatePair p).1 (griessCoordinatePair p).2 +
        P (griessCoordinatePair p).2 (griessCoordinatePair p).1) := by
  have ho (i j : Fin 24) :
      griessShortVector (Sum.inl (1, p)) i * griessShortVector (Sum.inl (1, p)) j =
        2 * (trialityPairProjection p i j + trialityPairMatrix p i j) := by
    linarith [griessPair_outer_coordinate_sum p i j,
      griessPair_outer_coordinate_difference p i j]
  unfold conwayShortPairing
  simp_rw [mul_assoc, ho]
  simp only [trialityPairProjection, Matrix.diagonal_apply, trialityPairMatrix_apply]
  simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
    ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- The original projection is symmetric, with no assumed matrix property. -/
theorem generatedFeasibleEighthExplicitProjectionNumerator_symmetric : ∀ i j : Fin 24,
    generatedFeasibleEighthExplicitProjectionNumerator i j =
      generatedFeasibleEighthExplicitProjectionNumerator j i := by
  decide +kernel

/-- Every actual pair coordinate except the genuine first minus root is zero. -/
theorem generatedFeasibleEighthExplicitIncoming_pair_zero (s : Fin 2) (p : Fin 276)
    (hp : ¬ (s = 0 ∧ griessCoordinatePair p = (0, 1))) :
    (griessConwayEncode generatedFeasibleEighthExplicitIncoming).2.1 (Sum.inl (s, p)) = 0 := by
  by_contra hn
  have h := generatedFeasibleContaining_source_nonzero_pairing
    generatedFeasibleEighthExplicitLocalWord (Sum.inl (s, p)) hn
  change conwayShortPairing (griessConwayEncode generatedFeasibleEighthExplicitIncoming).1
    (Sum.inl (s, p)) = 4 at h
  have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  have hc : generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).1 (griessCoordinatePair p).1 +
        generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).2 (griessCoordinatePair p).2 +
        2 * (if s = 0 then (-1 : ℤ) else 1) *
          generatedFeasibleEighthExplicitProjectionNumerator
            (griessCoordinatePair p).1 (griessCoordinatePair p).2 = 32 := by
    rcases hs with rfl | rfl
    · rw [generatedFeasibleContaining_minus_pairing] at h
      rw [generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).1
        (griessCoordinatePair p).1,
        generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).2
          (griessCoordinatePair p).2,
        generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).1
          (griessCoordinatePair p).2,
        generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).2
          (griessCoordinatePair p).1] at h
      rw [generatedFeasibleEighthExplicitProjectionNumerator_symmetric
        (griessCoordinatePair p).2 (griessCoordinatePair p).1] at h
      exact_mod_cast (show
        (generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).1 (griessCoordinatePair p).1 : ℝ) +
        (generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).2 (griessCoordinatePair p).2 : ℝ) +
        2 * (-1 : ℝ) * (generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) = 32 by linarith)
    · rw [generatedFeasibleContaining_plus_pairing] at h
      rw [generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).1
        (griessCoordinatePair p).1,
        generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).2
          (griessCoordinatePair p).2,
        generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).1
          (griessCoordinatePair p).2,
        generatedFeasibleEighthExplicitIncoming_matrix (griessCoordinatePair p).2
          (griessCoordinatePair p).1] at h
      rw [generatedFeasibleEighthExplicitProjectionNumerator_symmetric
        (griessCoordinatePair p).2 (griessCoordinatePair p).1] at h
      exact_mod_cast (show
        (generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).1 (griessCoordinatePair p).1 : ℝ) +
        (generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).2 (griessCoordinatePair p).2 : ℝ) +
        2 * (1 : ℝ) * (generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) = 32 by linarith)
  exact hp ((generatedFeasibleEighthExplicitProjectionNumerator_pair_characterization s p).mp hc)

/-- The phase-correct explicit incoming vector is an actual whole containing orbit vector. -/
theorem generatedFeasibleEighthExplicitIncoming_orbit :
    generatedFeasibleEighthExplicitIncoming ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination :=
  ⟨⟨localFiberIntoH generatedFeasibleEighthExplicitLocalWord,
    generatedFeasibleEighthExplicitLocalWord_first⟩, rfl⟩

/-- The entire preferred pair block consists of the single genuine first root with phase zero.
-/
theorem generatedFeasibleEighthExplicitIncoming_pair (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedFeasibleEighthExplicitIncoming).2.1 (Sum.inl (s, p)) =
      if s = 0 ∧ griessCoordinatePair p = (0, 1) then 1 else 0 := by
  by_cases h : s = 0 ∧ griessCoordinatePair p = (0, 1)
  · obtain ⟨rfl, hp⟩ := h
    have he : p = generatedFeasiblePhysicalRootPair := by
      apply griessCoordinatePairEquiv.injective
      apply Subtype.ext
      change griessCoordinatePair p = griessCoordinatePair generatedFeasiblePhysicalRootPair
      rw [hp, generatedFeasiblePhysicalRootPair_coordinates]
    subst p
    rw [ite_eq_left ⟨rfl, generatedFeasiblePhysicalRootPair_coordinates⟩]
    exact generatedFeasibleContaining_first_coordinate _
      generatedFeasibleEighthExplicitIncoming_orbit
  · rw [ite_eq_right h]
    exact generatedFeasibleEighthExplicitIncoming_pair_zero s p h

/-- The original code label of the coordinate octad detected by the actual final matrix. -/
def generatedFeasibleEighthFlagOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨(⟨2333, by decide⟩ : Fin 4096), by decide +kernel⟩

theorem generatedFeasibleEighthFlagOctad_label :
    golayOctadLabel generatedFeasibleEighthFlagOctad = 2333 := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨(⟨2333, by decide⟩ : Fin 4096), by decide +kernel⟩)

/-- The actual octad projector is bound to every original coordinate of code label 2333. -/
theorem generatedFeasibleEighthFlagOctad_projection :
    generatedAxisE8ShortProjection generatedFeasibleEighthFlagOctad =
      Matrix.diagonal (fun i : Fin 24 =>
        if (golayEncodedMask 2333).testBit i.val then (1 : ℝ) else 0) := by
  have hz : ∀ i : Fin 24,
      golayEncoder (golayLabelCoefficients 2333) i = 0 ↔
        (golayEncodedMask 2333).testBit i.val = false := by decide +kernel
  unfold generatedAxisE8ShortProjection
  simp only [golayOctadWord, generatedFeasibleEighthFlagOctad_label]
  apply congrArg Matrix.diagonal
  funext i
  cases hb : (golayEncodedMask 2333).testBit i.val with
  | false => simp [hz, hb]
  | true => simp [hz, hb]

/-- The distinguished original mate line is genuinely incident in that actual octad. -/
theorem generatedFeasibleEighthFlagOctad_mate_incident :
    generatedFeasibleMateLabel ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFeasibleEighthFlagOctad)) := by
  rw [generatedAxisE8ShortLines_coordinate_mem]
  change generatedOctadPairSupport generatedFeasibleEighthFlagOctad
    generatedFeasiblePhysicalRootPair
  unfold generatedOctadPairSupport
  rw [generatedFeasibleEighthFlagOctad_label, generatedFeasiblePhysicalRootPair_coordinates]
  decide +kernel

/-- Every physical mate outer entry retains its actual normalization. -/
theorem generatedFeasibleEighth_mate_outer_entry (i j : Fin 24) :
    generatedAxisE8ShortOuter generatedFeasibleMateLabel i j =
      if (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) then 2 else 0 := by
  unfold generatedAxisE8ShortOuter
  simp only [Matrix.vecMulVec_apply, griessShortVector, generatedFeasibleMateLabel,
    griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates]
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  split_ifs <;> simp_all <;> norm_num

/-- Every actual final matrix diagonal is the exact coordinate octad/short flag diagonal. -/
theorem generatedFeasibleEighthExplicitDestination_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).1 i i =
      generatedAxisE8ShortFlagMatrix
        (generatedAxisE8ShortProjection generatedFeasibleEighthFlagOctad)
        (generatedAxisE8ShortOuter generatedFeasibleMateLabel) i i := by
  have hd : ∀ k : Fin 24,
      generatedFeasibleEighthExplicitProjectionNumerator k k =
        if k = 0 ∨ k = 1 then (10 : ℤ) else
          if (golayEncodedMask 2333).testBit k.val then 2 else 6 := by decide +kernel
  rw [generatedFeasibleEighthExplicitDestination, generatedFourth_triality_matrix_diagonal,
    generatedFeasibleEighthExplicitIncoming_matrix, hd]
  simp only [generatedAxisE8ShortFlagMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, generatedFeasibleEighthFlagOctad_projection,
    generatedFeasibleEighth_mate_outer_entry, Matrix.one_apply_eq,
    Matrix.diagonal_apply_eq, and_self]
  by_cases hi : i = 0 ∨ i = 1
  · have hb : (golayEncodedMask 2333).testBit i.val = true := by
      rcases hi with rfl | rfl <;> decide +kernel
    norm_num [hi, hb]
  · cases hb : (golayEncodedMask 2333).testBit i.val <;> norm_num [hi, hb]

/-- Every actual final off-diagonal entry is the exact distinguished mate outer entry. -/
theorem generatedFeasibleEighthExplicitDestination_matrix_off_diagonal
    (i j : Fin 24) (hij : i ≠ j) :
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).1 i j =
      generatedAxisE8ShortFlagMatrix
        (generatedAxisE8ShortProjection generatedFeasibleEighthFlagOctad)
        (generatedAxisE8ShortOuter generatedFeasibleMateLabel) i j := by
  have hp : griessCoordinatePair (griessPairIndex i j hij) = (0, 1) ↔
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    rw [griessPairIndex_coordinates]
    by_cases h : i < j
    · simp [h, Prod.mk.injEq]
      omega
    · simp [h, Prod.mk.injEq]
      omega
  rw [generatedFeasibleEighthExplicitDestination,
    generatedFourth_triality_matrix_off_diagonal _ i j hij,
    generatedFeasibleEighthExplicitIncoming_pair,
    generatedFeasibleEighthExplicitIncoming_pair]
  simp only [Fin.reduceEq, true_and, false_and, ite_false]
  simp only [generatedAxisE8ShortFlagMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, generatedFeasibleEighthFlagOctad_projection,
    generatedFeasibleEighth_mate_outer_entry, Matrix.one_apply_ne hij,
    Matrix.diagonal_apply_ne _ hij]
  by_cases hc : griessCoordinatePair (griessPairIndex i j hij) = (0, 1)
  · have hs : (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) := by
      rcases hp.mp hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    norm_num [hc, hs]
  · have hs : ¬ ((i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1)) := by
      rintro ⟨h0, h1⟩
      rcases h0 with rfl | rfl
      · rcases h1 with rfl | rfl
        · exact hij rfl
        · exact hc (hp.mpr (Or.inl ⟨rfl, rfl⟩))
      · rcases h1 with rfl | rfl
        · exact hc (hp.mpr (Or.inr ⟨rfl, rfl⟩))
        · exact hij rfl
    norm_num [hc, hs]

/-- The complete actual final matrix has the original E8/short flag watermark. -/
theorem generatedFeasibleEighthExplicitDestination_matrix_flag :
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).1 =
      generatedAxisE8ShortFlagMatrix
        (generatedAxisE8ShortProjection generatedFeasibleEighthFlagOctad)
        (generatedAxisE8ShortOuter generatedFeasibleMateLabel) := by
  ext i j
  by_cases hij : i = j
  · subst j
    exact generatedFeasibleEighthExplicitDestination_matrix_diagonal i
  · exact generatedFeasibleEighthExplicitDestination_matrix_off_diagonal i j hij

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
