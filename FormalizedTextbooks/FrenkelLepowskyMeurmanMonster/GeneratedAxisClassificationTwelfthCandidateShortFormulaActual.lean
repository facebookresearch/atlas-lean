/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortFormulaData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateBlocks

/-! The complete actual candidate short block retains all three genuine triality source families. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Original incoming short coefficients and the entire genuine candidate tensor determine
all actual outgoing short coefficients, including zeros. -/
theorem generatedTwelfth_candidate_short_formula_generic_actual
    (hcache : ∀ r : GriessShortIndex, generatedAxisGlobalFifthRoot09Packet.2.1 r =
      (generatedTwelfthIncomingShortCoefficient r : ℝ) / 16)
    (htensor : ∀ (t : SpinIndex) (i : Fin 24),
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
        generatedFifthAxis)).2.2 t i =
        (generatedTwelfthIncomingSpinTensorOutputInteger (nortonUIntegerLabel t) i : ℝ) /
          (64 * Real.sqrt 2))
    (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.1 r =
      (generatedTwelfthCandidateShortFormula r : ℝ) := by
  have hm (i j : Fin 24) :
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
        generatedFifthAxis)).1 i j = (generatedTwelfthIncomingMatrixQ i j : ℝ) := by
    rw [generatedTwelfth_incoming_candidate_source_blocks.1,
      ← generatedAxisGlobalFifthRoot09Packet_actual]
    exact generatedTwelfth_incoming_matrix_coordinate i j
  have hc (s : GriessShortIndex) :
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
        generatedFifthAxis)).2.1 s = (generatedTwelfthIncomingShortCoefficient s : ℝ) / 16 := by
    rw [generatedTwelfth_incoming_candidate_source_blocks.2, hcache]
  change 128 * (griessConwayEncode
    (sExtra (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis))).2.1 r = _
  rw [generatedAxisGlobalRawTrialityFormula_actual]
  change 128 * generatedAxisGlobalRawTrialityShort
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis)) r = _
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp only [generatedAxisGlobalRawTrialityShort, generatedTwelfthCandidateShortFormula]
    rw [hm, hc, hc]
    push_cast
    split_ifs <;> ring
  · simp only [generatedAxisGlobalRawTrialityShort, generatedTwelfthCandidateShortFormula]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [hc]
    simp only [trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom,
      smul_eq_mul]
    ring
  · simp only [generatedAxisGlobalRawTrialityShort, generatedTwelfthCandidateShortFormula]
    rw [htensor, htensor]
    simp only [nortonUIntegerLabel_coeff]
    push_cast
    simp only [nortonUIntegerSign_real]
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp [hn]
    ring_nf
    simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
