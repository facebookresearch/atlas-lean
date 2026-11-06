/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenPhaseCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairPhaseCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives

/-! Complete finite original middle short packet, before the last canonical triality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Original 56 odd terms, 63 even terms, and all pair rows with their true zero coefficients. -/
abbrev GeneratedAxisGlobalCanonicalFourthMiddleShortIndex :=
  Fin 56 ⊕ (Fin 63 ⊕ (Fin 2 × Fin 276))

/-- Every term retains its original preferred-short label. -/
def generatedAxisGlobalCanonicalFourthMiddleShortLabel :
    GeneratedAxisGlobalCanonicalFourthMiddleShortIndex → GriessShortIndex
  | Sum.inl j => generatedFourthOddRootOutputLabel j
  | Sum.inr (Sum.inl j) => generatedFourthEvenRootOutputLabel j
  | Sum.inr (Sum.inr p) => Sum.inl p

/-- The exact original signed unit coefficients, including the sole negative pair. -/
def generatedAxisGlobalCanonicalFourthMiddleShortCoefficient :
    GeneratedAxisGlobalCanonicalFourthMiddleShortIndex → ℚ
  | Sum.inl j => (generatedAxisGlobalIntSign (generatedFourthOddCoefficientPhaseData j) : ℚ)
  | Sum.inr (Sum.inl j) => (generatedAxisGlobalIntSign (generatedFourthEvenCoefficientCache j) : ℚ)
  | Sum.inr (Sum.inr (s, p)) => if s = 1 ∧ griessCoordinatePair p = (8, 11) then -1 else 0

/-- A finite sum contains every actual middle short coordinate. -/
def generatedAxisGlobalCanonicalFourthMiddleSparseShortQ (r : GriessShortIndex) : ℚ :=
  ∑ p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex,
    if generatedAxisGlobalCanonicalFourthMiddleShortLabel p = r then
      generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p else 0

private theorem fourth_middle_odd_sparse (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1
      (Sum.inr (Sum.inr (d, i))) =
    ∑ j : Fin 56, if generatedFourthOddRootOutputLabel j = Sum.inr (Sum.inr (d, i)) then
      qSign (generatedFourthOddCoefficientPhaseData j) else 0 := by
  by_cases h : ∃ j : Fin 56, generatedFourthOddRootOutputData j = (d, i)
  · obtain ⟨j, hj⟩ := h
    have hl : generatedFourthOddRootOutputLabel j = Sum.inr (Sum.inr (d, i)) := by
      simp [generatedFourthOddRootOutputLabel, hj]
    rw [← hl, generatedFourth_odd_middle_coefficient]
    symm
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      have hn : generatedFourthOddRootOutputLabel k ≠ generatedFourthOddRootOutputLabel j := by
        intro he
        apply hk
        apply generatedFourthOddRootOutputData_injective
        simpa only [generatedFourthOddRootOutputLabel, Sum.inr.injEq] using he
      simp [hn]
    · simp
  · have hz : (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1
        (Sum.inr (Sum.inr (d, i))) = 0 := by
      rw [generatedFourth_local_short]
      exact not_ne_iff.mp (fun hn => h ((generatedFourth_odd_middle_nonzero_iff d i).mp hn))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hn : generatedFourthOddRootOutputLabel j ≠ Sum.inr (Sum.inr (d, i)) := by
      intro he
      apply h
      refine ⟨j, ?_⟩
      simpa only [generatedFourthOddRootOutputLabel, Sum.inr.injEq] using he
    simp [hn]

/-- Every rational finite middle coefficient is the complete actual original coefficient. -/
theorem generatedAxisGlobalCanonicalFourthMiddleSparseShortQ_actual (r : GriessShortIndex) :
    (generatedAxisGlobalCanonicalFourthMiddleSparseShortQ r : ℝ) =
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1 r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rw [generatedFourth_local_short, generatedFourth_transported_pair_coordinate,
      generatedFourth_pair_phase_zero]
    simp [generatedAxisGlobalCanonicalFourthMiddleSparseShortQ,
      generatedAxisGlobalCanonicalFourthMiddleShortLabel,
      generatedAxisGlobalCanonicalFourthMiddleShortCoefficient,
      generatedFourthOddRootOutputLabel, generatedFourthEvenRootOutputLabel,
      Fintype.sum_sum_type, apply_ite]
  · rw [generatedFourth_local_short, generatedFourth_middle_octad_sparse_cache]
    simp only [generatedAxisGlobalCanonicalFourthMiddleSparseShortQ, Fintype.sum_sum_type,
      generatedAxisGlobalCanonicalFourthMiddleShortLabel,
      generatedAxisGlobalCanonicalFourthMiddleShortCoefficient]
    simp only [generatedFourthOddRootOutputLabel, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, ite_false, Finset.sum_const_zero,
      add_zero, zero_add, Rat.cast_sum, apply_ite, Rat.cast_zero, Rat.cast_intCast,
      generatedAxisGlobalIntSign_real]
  · rw [fourth_middle_odd_sparse]
    simp only [generatedAxisGlobalCanonicalFourthMiddleSparseShortQ, Fintype.sum_sum_type,
      generatedAxisGlobalCanonicalFourthMiddleShortLabel,
      generatedAxisGlobalCanonicalFourthMiddleShortCoefficient]
    simp only [generatedFourthEvenRootOutputLabel, Sum.inr.injEq, Sum.inl_ne_inr,
      ite_false, Finset.sum_const_zero,
      add_zero, Rat.cast_sum, apply_ite, Rat.cast_zero, Rat.cast_intCast,
      generatedAxisGlobalIntSign_real]

/-- The entire genuine middle short constituent is its finite original preferred-basis sum. -/
theorem generatedAxisGlobalCanonicalFourthMiddleShortPacket_actual :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1 =
    ∑ p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex,
      (generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p : ℝ) •
        Pi.single (generatedAxisGlobalCanonicalFourthMiddleShortLabel p) (1 : ℝ) := by
  funext r
  rw [← generatedAxisGlobalCanonicalFourthMiddleSparseShortQ_actual]
  simp only [generatedAxisGlobalCanonicalFourthMiddleSparseShortQ, Rat.cast_sum,
    apply_ite, Rat.cast_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : generatedAxisGlobalCanonicalFourthMiddleShortLabel p = r <;> simp [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
