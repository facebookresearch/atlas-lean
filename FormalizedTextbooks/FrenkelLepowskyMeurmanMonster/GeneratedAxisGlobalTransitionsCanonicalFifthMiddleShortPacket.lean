/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumeratorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives

/-! The complete original 120-coordinate short constituent before the final Fifth triality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The 64 original odd labels and 56 original octad labels. -/
abbrev GeneratedAxisGlobalCanonicalFifthMiddleShortIndex := Fin 64 ⊕ Fin 56

/-- Every term uses its genuine original preferred-short label. -/
def generatedAxisGlobalCanonicalFifthMiddleShortLabel :
    GeneratedAxisGlobalCanonicalFifthMiddleShortIndex → GriessShortIndex
  | Sum.inl j => generatedFifthOddRootOutputLabel j
  | Sum.inr j => generatedFifthEvenRootOutputLabel j

/-- Each coefficient retains the complete original preferred-Q phase. -/
def generatedAxisGlobalCanonicalFifthMiddleShortCoefficient :
    GeneratedAxisGlobalCanonicalFifthMiddleShortIndex → ℚ
  | Sum.inl j => (generatedAxisGlobalIntSign (generatedFifthOddCoefficientPhaseData j) : ℚ)
  | Sum.inr j => (generatedAxisGlobalIntSign (generatedFifthEvenCoefficientCache j) : ℚ)

/-- The entire original middle axis. -/
def generatedAxisGlobalCanonicalFifthMiddleAxis : GriessSpace :=
  rhoLocal (localFiberIntoH generatedFifthLocalFiber)
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))

/-- All original short packet labels are distinct. -/
theorem generatedAxisGlobalCanonicalFifthMiddleShortLabel_injective :
    Function.Injective generatedAxisGlobalCanonicalFifthMiddleShortLabel := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · congr 1
    apply generatedFifthOddRootOutputData_injective
    simpa only [generatedAxisGlobalCanonicalFifthMiddleShortLabel,
      generatedFifthOddRootOutputLabel, Sum.inr.injEq] using h
  · simp only [generatedAxisGlobalCanonicalFifthMiddleShortLabel,
      generatedFifthOddRootOutputLabel, generatedFifthEvenRootOutputLabel,
      Sum.inr.injEq, reduceCtorEq] at h
  · simp only [generatedAxisGlobalCanonicalFifthMiddleShortLabel,
      generatedFifthOddRootOutputLabel, generatedFifthEvenRootOutputLabel,
      Sum.inr.injEq, reduceCtorEq] at h
  · congr 1
    apply generatedFifth_even_octads_injective
    have hp : (generatedFifthEvenRootOctad a, generatedFifthEvenRootSign a) =
        (generatedFifthEvenRootOctad b, generatedFifthEvenRootSign b) := by
      simpa only [generatedAxisGlobalCanonicalFifthMiddleShortLabel,
        generatedFifthEvenRootOutputLabel, Sum.inr.injEq, Sum.inl.injEq] using h
    exact congrArg Prod.fst hp

/-- Every displayed coefficient is the complete actual original middle coefficient. -/
theorem generatedAxisGlobalCanonicalFifthMiddleShortCoefficient_actual
    (p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex) :
    (griessConwayEncode generatedAxisGlobalCanonicalFifthMiddleAxis).2.1
      (generatedAxisGlobalCanonicalFifthMiddleShortLabel p) =
        (generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p : ℝ) := by
  rcases p with j | j
  · simpa only [generatedAxisGlobalCanonicalFifthMiddleAxis,
      generatedAxisGlobalCanonicalFifthMiddleShortLabel,
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient,
      Rat.cast_intCast, generatedAxisGlobalIntSign_real] using
        generatedFifth_odd_middle_coefficient j
  · simpa only [generatedAxisGlobalCanonicalFifthMiddleAxis,
      generatedAxisGlobalCanonicalFifthMiddleShortLabel,
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient,
      Rat.cast_intCast, generatedAxisGlobalIntSign_real,
      generatedFifth_even_coefficient_cache] using generatedFifth_even_middle_coefficient j

/-- The finite original preferred-basis sum contains every actual middle short coordinate. -/
theorem generatedAxisGlobalCanonicalFifthMiddleShortPacket_actual :
    (griessConwayEncode generatedAxisGlobalCanonicalFifthMiddleAxis).2.1 =
      ∑ p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex,
        (generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p : ℝ) •
          Pi.single (generatedAxisGlobalCanonicalFifthMiddleShortLabel p) (1 : ℝ) := by
  funext r
  by_cases h : ∃ p, generatedAxisGlobalCanonicalFifthMiddleShortLabel p = r
  · obtain ⟨p, rfl⟩ := h
    rw [generatedAxisGlobalCanonicalFifthMiddleShortCoefficient_actual]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hqp
      have hn := fun he => hqp (generatedAxisGlobalCanonicalFifthMiddleShortLabel_injective he)
      simp [Ne.symm hn]
    · simp
  · have hz : (griessConwayEncode generatedAxisGlobalCanonicalFifthMiddleAxis).2.1 r = 0 := by
      apply not_ne_iff.mp
      intro hn
      rw [generatedAxisGlobalCanonicalFifthMiddleAxis, generatedFourth_local_short] at hn
      rcases (generatedFifth_middle_nonzero_iff r).mp hn with ⟨j,hj⟩ | ⟨j,hj⟩
      · exact h ⟨Sum.inl j,hj⟩
      · exact h ⟨Sum.inr j,hj⟩
    rw [hz]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    symm
    apply Finset.sum_eq_zero
    intro p _
    have hn : generatedAxisGlobalCanonicalFifthMiddleShortLabel p ≠ r := fun he => h ⟨p,he⟩
    simp [hn]

/-- The entire finite original preferred short constituent in rational coordinates. -/
def generatedAxisGlobalCanonicalFifthMiddleSparseShortQ (r : GriessShortIndex) : ℚ :=
  ∑ p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex,
    if generatedAxisGlobalCanonicalFifthMiddleShortLabel p = r then
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p else 0

/-- The finite rational sum equals every actual original middle short coordinate. -/
theorem generatedAxisGlobalCanonicalFifthMiddleSparseShortQ_actual (r : GriessShortIndex) :
    (generatedAxisGlobalCanonicalFifthMiddleSparseShortQ r : ℝ) =
      (griessConwayEncode generatedAxisGlobalCanonicalFifthMiddleAxis).2.1 r := by
  rw [generatedAxisGlobalCanonicalFifthMiddleShortPacket_actual]
  simp only [generatedAxisGlobalCanonicalFifthMiddleSparseShortQ, Rat.cast_sum,
    apply_ite, Rat.cast_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : generatedAxisGlobalCanonicalFifthMiddleShortLabel p = r <;> simp [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
