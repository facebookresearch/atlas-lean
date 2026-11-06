/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForwardCodeProjection

/-! Actual matrix projection of forward triality conjugates of arbitrary even Q elements. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Even modulation makes the actual pair-short phase the encoded translation character. -/
theorem generatedEvenQ_pair_phase (q : Q) (d : Fin 4096)
    (hd : spinTranslation q = golayLabelCoefficients d) (he : spinModulation q 11 = 0)
    (s : Fin 2) (p : Fin 276) :
    localShortPhase (localFiberIncl q) (Sum.inl (s,p)) =
      golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2 := by
  change toAdd (spinConjugation (spinHolomorphIncl q)
    (griessShortQ (Sum.inl (s,p)))).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero, qBeta_spin_coordinates, qBeta_spin_coordinates,
    hd, griessPairQ_translation, griessPairQ_modulation]
  rw [spinDot_comm (golayLabelCoefficients d), griessPairSyndrome_dot]
  have ht : spinDot (Pi.single 11 1) (spinModulation q) = 0 := by
    simp [spinDot, Pi.single_apply, he]
  split_ifs
  · simp [spinDot]
  · rw [ht, add_zero]

/-- The code lift multiplies each short pair coordinate by its encoded character. -/
theorem generatedEvenQ_short_pair (q : Q) (d : Fin 4096)
    (hd : spinTranslation q = golayLabelCoefficients d) (he : spinModulation q 11 = 0)
    (x : GriessShortIndex → ℝ) (s : Fin 2) (p : Fin 276) :
    localShortRepresentation (localFiberIncl q) x (Sum.inl (s,p)) =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          x (Sum.inl (s,p)) := by
  have hp : griessShortPermutation (localFiberIncl q).val.2
      (Sum.inl (s,p)) = Sum.inl (s,p) := by
    change griessShortPermutation 1 (Sum.inl (s,p)) = Sum.inl (s,p)
    rw [map_one]; rfl
  have hg := localShortOperator_image (localFiberIncl q) x (Sum.inl (s,p))
  rw [hp, generatedEvenQ_pair_phase q d hd he] at hg
  exact hg

/-- The source code action fixes all diagonal dictionary coordinates. -/
theorem generatedEvenQ_blocks_diagonal (q : Q) (x : GriessSpace) :
    (trialityBlocksEquiv (rhoLocal (inclQ q) x)).1 =
      (trialityBlocksEquiv x).1 := by
  have hg := localGriessRepresentation_encode (localFiberIncl q) x
  have hm := congrArg (fun b : ConwayRawSpace => b.1) hg
  change (griessConwayEncode (rhoLocal (inclQ q) x)).1 =
    conwayMatrixAction 1 (griessConwayEncode x).1 at hm
  rw [map_one] at hm
  funext i
  have hi := congrFun (congrFun hm i) i
  simpa only [griessConwayEncode, dite_true, LinearEquiv.coe_one, id_eq] using hi

/-- The C row of the actual even Q action is its physical sign character. -/
theorem generatedEvenQ_blocks_C (q : Q) (d : Fin 4096)
    (hd : spinTranslation q = golayLabelCoefficients d) (he : spinModulation q 11 = 0)
    (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ q) x)).2.1 2 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 2 p := by
  have hg := localGriessRepresentation_encode (localFiberIncl q) x
  have h0 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (0,p))) hg
  have h1 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (1,p))) hg
  change (griessConwayEncode (rhoLocal (inclQ q) x)).2.1 (Sum.inl (0,p)) =
    localShortRepresentation (localFiberIncl q) (griessConwayEncode x).2.1
      (Sum.inl (0,p)) at h0
  change (griessConwayEncode (rhoLocal (inclQ q) x)).2.1 (Sum.inl (1,p)) =
    localShortRepresentation (localFiberIncl q) (griessConwayEncode x).2.1
      (Sum.inl (1,p)) at h1
  rw [generatedEvenQ_short_pair q d hd he] at h0 h1
  simp only [griessConwayEncode, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h0 h1
  linarith

/-- The forward conjugate fixes all physical diagonal matrix entries. -/
theorem generatedForwardQ_blocks_diagonal (q : Q) (x : GriessSpace) :
    (trialityBlocksEquiv (sExtra (rhoLocal (inclQ q) (sExtra⁻¹ x)))).1 =
      (trialityBlocksEquiv x).1 := by
  rw [generatedExtra_blocks_diagonal, generatedEvenQ_blocks_diagonal q,
    generatedExtra_inverse_blocks_diagonal]

/-- The forward conjugate multiplies A by the actual encoded Golay pair character. -/
theorem generatedForwardQ_blocks_A (q : Q) (d : Fin 4096)
    (hd : spinTranslation q = golayLabelCoefficients d) (he : spinModulation q 11 = 0)
    (x : GriessSpace)
    (p : Fin 276) :
    (trialityBlocksEquiv (sExtra
      (rhoLocal (inclQ q) (sExtra⁻¹ x)))).2.1 0 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 0 p := by
  rw [generatedForwardExtra_blocks_A, generatedEvenQ_blocks_C q d hd he,
    generatedForwardExtra_inverse_blocks_C]

/-- The entire A matrix block of the forward triality conjugate is the actual Golay sign action.
The local membership and quotient projection are separate consequences of the
full centralizer identification and the matrix-action kernel. -/
theorem generatedForwardQ_matrix (q : Q) (d : Fin 4096)
    (hd : spinTranslation q = golayLabelCoefficients d) (he : spinModulation q 11 = 0)
    (x : GriessSpace) :
    (griessConwayEncode (sExtra (rhoLocal (inclQ q) (sExtra⁻¹ x)))).1 =
      conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d))
        (griessConwayEncode x).1 := by
  ext i j
  rw [sourceGeneratedSign_matrix_apply]
  by_cases hij : i = j
  · subst j
    simp only [griessConwayEncode, dite_true, generatedForwardQ_blocks_diagonal q,
      CharTwo.add_self_eq_zero, qSign_zero, one_mul]
  · have hp : golayEncoder (golayLabelCoefficients d)
        (griessCoordinatePair (griessPairIndex i j hij)).1 +
        golayEncoder (golayLabelCoefficients d)
          (griessCoordinatePair (griessPairIndex i j hij)).2 =
        golayEncoder (golayLabelCoefficients d) i + golayEncoder (golayLabelCoefficients d) j := by
      rw [griessPairIndex_coordinates]
      split_ifs
      · rfl
      · exact add_comm _ _
    simp only [griessConwayEncode, hij, dite_false]
    rw [generatedForwardQ_blocks_A q d hd he, hp]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
