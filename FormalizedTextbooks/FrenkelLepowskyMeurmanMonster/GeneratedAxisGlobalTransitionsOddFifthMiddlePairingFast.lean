/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortTargets

/-! Complete finite pairing formulas use only certified original selected preferred-short coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The full original candidate coefficient at a selected target, with the complete central correction. -/
def generatedAxisGlobalOddFifthSelectedShortQ (k : Fin 2) (j : Fin 4136) : ℚ :=
  (generatedAxisGlobalIntSign (generatedAxisGlobalOddFifthSelectedPhase k j) : ℚ) *
    (generatedAxisGlobalOddFifthOutgoingPacket k).2.1 (generatedAxisGlobalOddFifthSelectedSource k j)

/-- A complete actual inverse preferred-Q certificate identifies the true rational framed coefficient. -/
theorem generatedAxisGlobalOddFifthSelectedShortQ_actual (k : Fin 2) (j : Fin 4136)
    (hq : spinConjugation ((generatedAxisGlobalOddFifthComparisonFiber k)⁻¹).val.1
      (griessShortQ (generatedAxisGlobalOddFifthSelectedTarget j)) =
      qCentral (generatedAxisGlobalOddFifthSelectedPhase k j) *
        griessShortQ (generatedAxisGlobalOddFifthSelectedSource k j)) :
    generatedAxisGlobalOddFifthFramedShort k (generatedAxisGlobalOddFifthSelectedTarget j) =
      generatedAxisGlobalOddFifthSelectedShortQ k j := by
  apply Rat.cast_injective (α := ℝ)
  have h := generatedAxisGlobalOddFifthSelectedShort_actual k j hq
    ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis)
  rw [generatedAxisGlobalOddFifthFramedPacket_actual,
    generatedAxisGlobalOddFifthOutgoingPacket_actual] at h
  simpa only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalOddFifthFramedPacket,
    generatedAxisGlobalOddFifthSelectedShortQ, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real] using h

/-- Every needed inverse matrix coefficient uses the original selected pair rows. -/
def generatedAxisGlobalOddFifthMiddleMatrixFastQ (k : Fin 2) (i j : Fin 24) : ℚ :=
  if i = j then generatedAxisGlobalOddFifthFramedMatrix k i i else
    (generatedAxisGlobalOddFifthSelectedShortQ k
      (generatedAxisGlobalOddFifthSelectedPair 0 (generatedAxisGlobalFinitePairIndex i j)) -
    generatedAxisGlobalOddFifthSelectedShortQ k
      (generatedAxisGlobalOddFifthSelectedPair 1 (generatedAxisGlobalFinitePairIndex i j))) / 2

/-- The original inverse short formula at each actual canonical middle support term. -/
def generatedAxisGlobalOddFifthMiddleShortFastQ (k : Fin 2) :
    GeneratedAxisGlobalCanonicalFifthMiddleShortIndex → ℚ
  | Sum.inl j => generatedAxisGlobalInverseShortQ (generatedAxisGlobalOddFifthFramedPacket k)
      (generatedFifthOddRootOutputLabel j)
  | Sum.inr j => ∑ f : Fin 64,
      (trialityIntegerMatrix f (generatedFifthEvenRootSign j) : ℚ) / 8 *
        generatedAxisGlobalOddFifthSelectedShortQ k (generatedAxisGlobalOddFifthSelectedEven j f)

/-- The complete finite pairing, with guards on the original actual zero support coefficients. -/
def generatedAxisGlobalOddFifthMiddlePairingFastQ (k : Fin 2) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24,
    if generatedAxisGlobalFifthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFifthMiddleMatrixFastQ k i j *
        generatedAxisGlobalFifthMiddleMatrixQ i j) +
  (∑ p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex,
    if generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p = 0 then 0 else
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p *
        generatedAxisGlobalOddFifthMiddleShortFastQ k p)

/-- Every inverse matrix coefficient in the pairing is exactly the complete actual inverse coefficient. -/
theorem generatedAxisGlobalOddFifthMiddleMatrixFastQ_eq (k : Fin 2)
    (hc : ∀ q : Fin 4136, generatedAxisGlobalOddFifthFramedShort k
      (generatedAxisGlobalOddFifthSelectedTarget q) = generatedAxisGlobalOddFifthSelectedShortQ k q)
    (i j : Fin 24) :
    generatedAxisGlobalOddFifthMiddleMatrixFastQ k i j =
      generatedAxisGlobalInverseMatrixQ (generatedAxisGlobalOddFifthFramedPacket k) i j := by
  have hp (s : Fin 2) (p : Fin 276) :
      generatedAxisGlobalOddFifthFramedShort k (Sum.inl (s,p)) =
      generatedAxisGlobalOddFifthSelectedShortQ k (generatedAxisGlobalOddFifthSelectedPair s p) := by
    simpa only [generatedAxisGlobalOddFifthSelectedPair_actual] using
      hc (generatedAxisGlobalOddFifthSelectedPair s p)
  simp only [generatedAxisGlobalOddFifthMiddleMatrixFastQ, generatedAxisGlobalInverseMatrixQ,
    generatedAxisGlobalOddFifthFramedPacket]
  split_ifs <;> simp only [hp]

/-- Every finite support inverse short coefficient is the complete actual inverse coefficient. -/
theorem generatedAxisGlobalOddFifthMiddleShortFastQ_eq (k : Fin 2)
    (hc : ∀ q : Fin 4136, generatedAxisGlobalOddFifthFramedShort k
      (generatedAxisGlobalOddFifthSelectedTarget q) = generatedAxisGlobalOddFifthSelectedShortQ k q)
    (p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex) :
    generatedAxisGlobalOddFifthMiddleShortFastQ k p =
      generatedAxisGlobalInverseShortQ (generatedAxisGlobalOddFifthFramedPacket k)
        (generatedAxisGlobalCanonicalFifthMiddleShortLabel p) := by
  rcases p with j | j
  · rfl
  · simp only [generatedAxisGlobalOddFifthMiddleShortFastQ,
      generatedAxisGlobalCanonicalFifthMiddleShortLabel, generatedFifthEvenRootOutputLabel,
      generatedAxisGlobalInverseShortQ, generatedAxisGlobalOddFifthFramedPacket]
    apply Finset.sum_congr rfl
    intro f _
    have h := hc (generatedAxisGlobalOddFifthSelectedEven j f)
    rw [generatedAxisGlobalOddFifthSelectedEven_actual] at h
    rw [h]

/-- All selected complete certificates make the fast finite expression the entire actual pairing. -/
theorem generatedAxisGlobalOddFifthMiddlePairingFastQ_eq (k : Fin 2)
    (hc : ∀ q : Fin 4136, generatedAxisGlobalOddFifthFramedShort k
      (generatedAxisGlobalOddFifthSelectedTarget q) = generatedAxisGlobalOddFifthSelectedShortQ k q) :
    generatedAxisGlobalOddFifthMiddlePairingFastQ k = generatedAxisGlobalOddFifthMiddlePairingQ k := by
  unfold generatedAxisGlobalOddFifthMiddlePairingFastQ generatedAxisGlobalOddFifthMiddlePairingQ
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : generatedAxisGlobalFifthMiddleMatrixQ i j = 0
    · simp only [h, ↓reduceIte, mul_zero]
    · rw [ite_eq_right h, generatedAxisGlobalOddFifthMiddleMatrixFastQ_eq k hc]
  · apply Finset.sum_congr rfl
    intro p _
    by_cases h : generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p = 0
    · simp only [h, ↓reduceIte, zero_mul]
    · rw [ite_eq_right h, generatedAxisGlobalOddFifthMiddleShortFastQ_eq k hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
