/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortPhases

/-! Exact rational coefficients of every actual fifth short-packet entry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All packet coefficients as rational numbers, with the checked original central signs. -/
def generatedAxisGlobalFifthShortRationalCoefficient :
    GeneratedAxisGlobalFifthShortPacketIndex → ℚ
  | Sum.inl (s, p) => if s = 0 then
      generatedAxisGlobalFifthMiddleMatrixQ
        (griessCoordinatePair p).1 (griessCoordinatePair p).2
    else -generatedAxisGlobalFifthMiddleMatrixQ
      (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | Sum.inr (j, e) =>
      (trialityIntegerMatrix e (generatedFifthEvenRootSign j) : ℚ) / 8 *
        (if generatedAxisGlobalFifthShortOctadPhaseData j = 0 then 1 else -1)

/-- These rational coefficients equal the complete actual real packet coefficients. -/
theorem generatedAxisGlobalFifthShortRationalCoefficient_actual
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    (generatedAxisGlobalFifthShortRationalCoefficient i : ℝ) =
      generatedAxisGlobalFifthShortPacketCoefficient i := by
  rcases i with ⟨s, p⟩ | ⟨j, e⟩
  · by_cases hs : s = 0 <;>
      simp [generatedAxisGlobalFifthShortRationalCoefficient,
        generatedAxisGlobalFifthShortPacketCoefficient, hs]
  · change _ = trialityRealMatrix e (generatedFifthEvenRootSign j) *
      qSign (generatedFifthEvenCoefficientPhase j)
    rw [generatedAxisGlobalFifthShortOctadPhase_actual]
    by_cases hj : generatedAxisGlobalFifthShortOctadPhaseData j = 0 <;>
      simp [generatedAxisGlobalFifthShortRationalCoefficient, trialityRealMatrix,
        Matrix.smul_apply, Matrix.map_apply, qSign, hj] <;> ring

/-- The entire actual short component is the explicitly signed rational preferred-basis packet. -/
theorem generatedAxisGlobalFifthShortRationalPacket_actual :
    (griessConwayEncode generatedFifthAxis).2.1 =
      ∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
        (generatedAxisGlobalFifthShortRationalCoefficient i : ℝ) •
          Pi.single (generatedAxisGlobalFifthShortPacketLabel i) (1 : ℝ) := by
  rw [← generatedAxisGlobalFifthShortPacket_eq]
  simp_rw [generatedAxisGlobalFifthShortRationalCoefficient_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
