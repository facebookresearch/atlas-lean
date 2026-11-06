/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortTargets

/-! Complete finite pairing formulas use only certified original selected preferred-short coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The full original candidate coefficient at a selected target, with the complete central correction. -/
def generatedAxisGlobalOddFourthSelectedShortQ (k : Fin 4) (j : Fin 4584) : ℚ :=
  (generatedAxisGlobalIntSign (generatedAxisGlobalOddFourthSelectedPhase k j) : ℚ) *
    (generatedAxisGlobalOddFourthOutgoingPacket k).2.1 (generatedAxisGlobalOddFourthSelectedSource k j)

/-- A complete actual inverse preferred-Q certificate identifies the true rational framed coefficient. -/
theorem generatedAxisGlobalOddFourthSelectedShortQ_actual (k : Fin 4) (j : Fin 4584)
    (hq : spinConjugation ((generatedAxisGlobalOddFourthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFourthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFourthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFourthSelectedSource k j)) :
    generatedAxisGlobalOddFourthFramedShort k (generatedAxisGlobalOddFourthSelectedTarget j) =
      generatedAxisGlobalOddFourthSelectedShortQ k j := by
  apply Rat.cast_injective (α := ℝ)
  have h := generatedAxisGlobalOddFourthSelectedShort_actual k j hq
    ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis)
  rw [generatedAxisGlobalOddFourthFramedPacket_actual,
    generatedAxisGlobalOddFourthOutgoingPacket_actual] at h
  simpa only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalOddFourthFramedPacket,
    generatedAxisGlobalOddFourthSelectedShortQ, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real] using h

/-- Every needed inverse matrix coefficient uses the original selected pair rows. -/
def generatedAxisGlobalOddFourthMiddleMatrixFastQ (k : Fin 4) (i j : Fin 24) : ℚ :=
  if i = j then generatedAxisGlobalOddFourthFramedMatrix k i i else
    (generatedAxisGlobalOddFourthSelectedShortQ k
      (generatedAxisGlobalOddFourthSelectedPair 0 (generatedAxisGlobalFinitePairIndex i j)) -
    generatedAxisGlobalOddFourthSelectedShortQ k
      (generatedAxisGlobalOddFourthSelectedPair 1 (generatedAxisGlobalFinitePairIndex i j))) / 2

/-- The original inverse short formula at each actual canonical middle support term. -/
def generatedAxisGlobalOddFourthMiddleShortFastQ (k : Fin 4) :
    GeneratedAxisGlobalCanonicalFourthMiddleShortIndex → ℚ
  | Sum.inl j => generatedAxisGlobalInverseShortQ (generatedAxisGlobalOddFourthFramedPacket k)
      (generatedFourthOddRootOutputLabel j)
  | Sum.inr (Sum.inl j) => ∑ f : Fin 64,
      (trialityIntegerMatrix f (generatedFourthEvenRootSign j) : ℚ) / 8 *
        generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedEven j f)
  | Sum.inr (Sum.inr (s,p)) =>
      if s = 0 then generatedAxisGlobalOddFourthFramedMatrix k
          (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
        (generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 0 p) +
          generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 1 p)) / 2
      else generatedAxisGlobalOddFourthFramedMatrix k
          (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 -
        (generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 0 p) +
          generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair 1 p)) / 2

/-- The complete finite pairing, with guards on the original actual zero support coefficients. -/
def generatedAxisGlobalOddFourthMiddlePairingFastQ (k : Fin 4) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24,
    if generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleMatrixFastQ k i j *
        generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j) +
  (∑ p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex,
    if generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p = 0 then 0 else
      generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p *
        generatedAxisGlobalOddFourthMiddleShortFastQ k p)

/-- Every inverse matrix coefficient in the pairing is exactly the complete actual inverse coefficient. -/
theorem generatedAxisGlobalOddFourthMiddleMatrixFastQ_eq (k : Fin 4)
    (hc : ∀ q : Fin 4584, generatedAxisGlobalOddFourthFramedShort k
      (generatedAxisGlobalOddFourthSelectedTarget q) = generatedAxisGlobalOddFourthSelectedShortQ k q)
    (i j : Fin 24) :
    generatedAxisGlobalOddFourthMiddleMatrixFastQ k i j =
      generatedAxisGlobalInverseMatrixQ (generatedAxisGlobalOddFourthFramedPacket k) i j := by
  have hp (s : Fin 2) (p : Fin 276) :
      generatedAxisGlobalOddFourthFramedShort k (Sum.inl (s,p)) =
      generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair s p) := by
    simpa only [generatedAxisGlobalOddFourthSelectedPair_actual] using
      hc (generatedAxisGlobalOddFourthSelectedPair s p)
  simp only [generatedAxisGlobalOddFourthMiddleMatrixFastQ, generatedAxisGlobalInverseMatrixQ,
    generatedAxisGlobalOddFourthFramedPacket]
  split_ifs <;> simp only [hp]

/-- Every finite support inverse short coefficient is the complete actual inverse coefficient. -/
theorem generatedAxisGlobalOddFourthMiddleShortFastQ_eq (k : Fin 4)
    (hc : ∀ q : Fin 4584, generatedAxisGlobalOddFourthFramedShort k
      (generatedAxisGlobalOddFourthSelectedTarget q) = generatedAxisGlobalOddFourthSelectedShortQ k q)
    (p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex) :
    generatedAxisGlobalOddFourthMiddleShortFastQ k p =
      generatedAxisGlobalInverseShortQ (generatedAxisGlobalOddFourthFramedPacket k)
        (generatedAxisGlobalCanonicalFourthMiddleShortLabel p) := by
  rcases p with j | (j | ⟨s,p⟩)
  · rfl
  · simp only [generatedAxisGlobalOddFourthMiddleShortFastQ,
      generatedAxisGlobalCanonicalFourthMiddleShortLabel, generatedFourthEvenRootOutputLabel,
      generatedAxisGlobalInverseShortQ, generatedAxisGlobalOddFourthFramedPacket]
    apply Finset.sum_congr rfl
    intro f _
    have h := hc (generatedAxisGlobalOddFourthSelectedEven j f)
    rw [generatedAxisGlobalOddFourthSelectedEven_actual] at h
    rw [h]
  · have hp (t : Fin 2) :
        generatedAxisGlobalOddFourthFramedShort k (Sum.inl (t,p)) =
          generatedAxisGlobalOddFourthSelectedShortQ k (generatedAxisGlobalOddFourthSelectedPair t p) := by
      simpa only [generatedAxisGlobalOddFourthSelectedPair_actual] using
        hc (generatedAxisGlobalOddFourthSelectedPair t p)
    simp only [generatedAxisGlobalOddFourthMiddleShortFastQ,
      generatedAxisGlobalCanonicalFourthMiddleShortLabel, generatedAxisGlobalInverseShortQ,
      generatedAxisGlobalOddFourthFramedPacket, hp]

/-- All selected complete certificates make the fast finite expression the entire actual pairing. -/
theorem generatedAxisGlobalOddFourthMiddlePairingFastQ_eq (k : Fin 4)
    (hc : ∀ q : Fin 4584, generatedAxisGlobalOddFourthFramedShort k
      (generatedAxisGlobalOddFourthSelectedTarget q) = generatedAxisGlobalOddFourthSelectedShortQ k q) :
    generatedAxisGlobalOddFourthMiddlePairingFastQ k = generatedAxisGlobalOddFourthMiddlePairingQ k := by
  unfold generatedAxisGlobalOddFourthMiddlePairingFastQ generatedAxisGlobalOddFourthMiddlePairingQ
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j = 0
    · simp only [h, ↓reduceIte, mul_zero]
    · rw [ite_eq_right h, generatedAxisGlobalOddFourthMiddleMatrixFastQ_eq k hc]
  · apply Finset.sum_congr rfl
    intro p _
    by_cases h : generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p = 0
    · simp only [h, ↓reduceIte, zero_mul]
    · rw [ite_eq_right h, generatedAxisGlobalOddFourthMiddleShortFastQ_eq k hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
