/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual extraspecial-image normalizer calculations for the source Gauss sums. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinProjection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- The representation wrapper has the already constructed coordinate operator. -/
theorem xiSpinLinearRepresentation_operator (q : Q) :
    spinLinearRepresentation q = spinOperator q := rfl

/-- Forgetting invertibility recovers the actual coordinate spin operator. -/
theorem xiSpinRepresentation_toLinearMap (q : Q) :
    (spinRepresentation q).toLinearMap = spinOperator q := rfl

/-- Evaluation of the actual coordinate spin operator. -/
theorem xiSpinOperator_apply (q : Q) (f : SpinSpace) (t : SpinIndex) :
    spinOperator q f t = qSign (spinPhase q t) * f (t + spinTranslation q) := rfl

set_option maxHeartbeats 2000000 in
-- The named group abbreviation requires additional unfolding for its central coordinate.
/-- Actual cocode commutation in the coordinate extraspecial group. -/
theorem xiGrayModulation_q_swap (a : XiGrayIndex) (q : Q) :
    xiGrayModulation (ofAdd a) * q =
      qCentral (spinDot (xiGrayCocode a) (spinTranslation q)) * q *
        xiGrayModulation (ofAdd a) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change binaryCocodeEmbedding (xiGrayCocode a) + toAdd q.base =
      (0 + toAdd q.base) + binaryCocodeEmbedding (xiGrayCocode a)
    abel
  · apply toAdd.injective
    change 0 + toAdd q.coeff + qBeta (binaryCocodeEmbedding (xiGrayCocode a)) (toAdd q.base) =
      (spinDot (xiGrayCocode a) (spinTranslation q) + toAdd q.coeff + qBeta 0 (toAdd q.base)) +
        0 + qBeta (0 + toAdd q.base) (binaryCocodeEmbedding (xiGrayCocode a))
    simp only [zero_add]
    have hl : qBeta (binaryCocodeEmbedding (xiGrayCocode a)) (toAdd q.base) = 0 := by
      simp [qBeta, binaryCocodeEmbedding]
    have hr : qBeta (toAdd q.base) (binaryCocodeEmbedding (xiGrayCocode a)) =
        spinDot (xiGrayCocode a) (spinTranslation q) := by
      simp only [qBeta, binaryCocodeEmbedding_right, spinDot, spinTranslation, mul_comm]
    rw [hl, hr, qBeta_zero_left]
    simp only [add_zero]
    have h := CharTwo.add_self_eq_zero (spinDot (xiGrayCocode a) (spinTranslation q))
    linear_combination -h

/-- Actual translation commutation in the coordinate extraspecial group. -/
theorem xiGrayTranslation_q_swap (a : XiGrayIndex) (q : Q) :
    xiGrayTranslation (ofAdd a) * q =
      qCentral (spinDot (spinModulation q) (xiGrayCode a)) * q *
        xiGrayTranslation (ofAdd a) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append (xiGrayCode a) (0 : SpinIndex) + toAdd q.base =
      (0 + toAdd q.base) + Fin.append (xiGrayCode a) (0 : SpinIndex)
    abel
  · apply toAdd.injective
    change 0 + toAdd q.coeff + qBeta (Fin.append (xiGrayCode a) (0 : SpinIndex)) (toAdd q.base) =
      (spinDot (spinModulation q) (xiGrayCode a) + toAdd q.coeff + qBeta 0 (toAdd q.base)) +
        0 + qBeta (0 + toAdd q.base) (Fin.append (xiGrayCode a) (0 : SpinIndex))
    simp only [zero_add]
    have hl : qBeta (Fin.append (xiGrayCode a) (0 : SpinIndex)) (toAdd q.base) =
        spinDot (spinModulation q) (xiGrayCode a) := by
      simp only [qBeta, Fin.append_left, spinDot, spinModulation, mul_comm]
    have hr : qBeta (toAdd q.base) (Fin.append (xiGrayCode a) (0 : SpinIndex)) = 0 := by
      simp only [qBeta, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [hl, hr, qBeta_zero_left]
    simp only [zero_add, add_comm]

/-- The represented central sign is the actual real scalar action. -/
theorem xiSpinOperator_central_mul (c : ZMod 2) (q r : Q) :
    spinOperator (qCentral c * q * r) = qSign c • (spinOperator q * spinOperator r) := by
  rw [spinOperator_mul, spinOperator_mul]
  apply LinearMap.ext
  intro f
  funext t
  change qSign (c + spinDot 0 t) * (spinOperator q (spinOperator r f)) (t + 0) =
    qSign c * (spinOperator q (spinOperator r f)) t
  simp

/-- Actual cocode commutation transported through the faithful spin representation. -/
theorem xiGrayModulation_spin_swap (a : XiGrayIndex) (q : Q) :
    spinOperator (xiGrayModulation (ofAdd a)) * spinOperator q =
      qSign (xiGrayBilinear a (xiGrayGammaProjection q)) •
        (spinOperator q * spinOperator (xiGrayModulation (ofAdd a))) := by
  rw [← xiGrayGammaProjection_pairing]
  have h := congrArg spinOperator (xiGrayModulation_q_swap a q)
  rw [spinOperator_mul, xiSpinOperator_central_mul] at h
  exact h

/-- Actual translation commutation transported through the faithful spin representation. -/
theorem xiGrayTranslation_spin_swap (a : XiGrayIndex) (q : Q) :
    spinOperator (xiGrayTranslation (ofAdd a)) * spinOperator q =
      qSign (xiGrayBilinear a (xiGrayGProjection q)) •
        (spinOperator q * spinOperator (xiGrayTranslation (ofAdd a))) := by
  rw [← xiGrayGProjection_pairing]
  have h := congrArg spinOperator (xiGrayTranslation_q_swap a q)
  rw [spinOperator_mul, xiSpinOperator_central_mul] at h
  exact h

/-- The explicitly computed element of Q after ξ_γ conjugation. -/
noncomputable def xiSpinGammaImage (q : Q) : Q :=
  qCentral (xiGrayQuadratic (xiGrayGammaProjection q)) * q *
    xiGrayModulation (ofAdd (xiGrayGammaProjection q))

/-- The explicitly computed element of Q after ξ_g conjugation. -/
noncomputable def xiSpinGImage (q : Q) : Q :=
  qCentral (xiGrayQuadratic (xiGrayGProjection q)) * q *
    xiGrayTranslation (ofAdd (xiGrayGProjection q))

theorem xiSpinGamma_conjugation (q : Q) :
    xiSpinGamma * spinOperator q * xiSpinGamma = spinOperator (xiSpinGammaImage q) := by
  rw [xiSpinGammaImage, xiSpinOperator_central_mul]
  exact xiGrayGaussian_conjugation _ _ _ (fun a => xiGrayModulation_spin_swap a q)

theorem xiSpinG_conjugation (q : Q) :
    xiSpinG * spinOperator q * xiSpinG = spinOperator (xiSpinGImage q) := by
  rw [xiSpinGImage, xiSpinOperator_central_mul]
  exact xiGrayGaussian_conjugation _ _ _ (fun a => xiGrayTranslation_spin_swap a q)

/-- The column source ξ has inverse ξ_γ ξ_g, and normalizes the actual spin image. -/
theorem xiSpinOperator_conjugation (q : Q) :
    xiSpinOperator * spinOperator q * (xiSpinGamma * xiSpinG) =
      spinOperator (xiSpinGImage (xiSpinGammaImage q)) := by
  unfold xiSpinOperator
  calc
    _ = xiSpinG * (xiSpinGamma * spinOperator q * xiSpinGamma) * xiSpinG := by
      simp only [mul_assoc]
    _ = _ := by rw [xiSpinGamma_conjugation, xiSpinG_conjugation]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
