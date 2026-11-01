/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual conjugation and orthogonal normalizer for the rank-four Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoGaussianData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Exact translation commutation in the normalized coordinate group. -/
theorem monsterNortonUTwoGaussianTranslation_q_swap (a : XiGrayIndex) (q : Q) :
    monsterNortonUTwoGaussianTranslation (ofAdd a) * q =
      qCentral (spinDot (spinModulation q) (monsterNortonUTwoGaussianCode a)) * q *
        monsterNortonUTwoGaussianTranslation (ofAdd a) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append (monsterNortonUTwoGaussianCode a) (0 : SpinIndex) + toAdd q.base =
      (0 + toAdd q.base) + Fin.append (monsterNortonUTwoGaussianCode a) (0 : SpinIndex)
    abel
  · apply toAdd.injective
    change 0 + toAdd q.coeff + qBeta (Fin.append (monsterNortonUTwoGaussianCode a) (0 :
      SpinIndex)) (toAdd q.base) =
      (spinDot (spinModulation q) (monsterNortonUTwoGaussianCode a) + toAdd q.coeff + qBeta 0
        (toAdd q.base)) +
        0 + qBeta (0 + toAdd q.base) (Fin.append (monsterNortonUTwoGaussianCode a) (0 : SpinIndex))
    simp only [zero_add]
    have hl : qBeta (Fin.append (monsterNortonUTwoGaussianCode a) (0 : SpinIndex)) (toAdd q.base) =
        spinDot (spinModulation q) (monsterNortonUTwoGaussianCode a) := by
      simp only [qBeta, Fin.append_left, spinDot, spinModulation, mul_comm]
    have hr : qBeta (toAdd q.base) (Fin.append (monsterNortonUTwoGaussianCode a) (0 :
      SpinIndex)) = 0 := by
      simp only [qBeta, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [hl, hr, qBeta_zero_left]
    simp only [zero_add, add_comm]

/-- Translation commutation transported through the actual spin representation. -/
theorem monsterNortonUTwoGaussianTranslation_spin_swap (a : XiGrayIndex) (q : Q) :
    spinOperator (monsterNortonUTwoGaussianTranslation (ofAdd a)) * spinOperator q =
      qSign (xiGrayBilinear a (monsterNortonUTwoGaussianProjection q)) •
        (spinOperator q * spinOperator (monsterNortonUTwoGaussianTranslation (ofAdd a))) := by
  rw [← monsterNortonUTwoGaussianProjection_pairing]
  have h := congrArg spinOperator (monsterNortonUTwoGaussianTranslation_q_swap a q)
  rw [spinOperator_mul, xiSpinOperator_central_mul] at h
  exact h

/-- The whole Q image, including its central coefficient. -/
noncomputable def monsterNortonUTwoGaussianImage (q : Q) : Q :=
  qCentral (xiGrayQuadratic (monsterNortonUTwoGaussianProjection q)) * q *
    monsterNortonUTwoGaussianTranslation (ofAdd (monsterNortonUTwoGaussianProjection q))

/-- The proved Gaussian conjugation specializes to the actual full Q formula. -/
theorem monsterNortonUTwoGaussian_conjugation (q : Q) :
    monsterNortonUTwoGaussian * spinOperator q * monsterNortonUTwoGaussian =
      spinOperator (monsterNortonUTwoGaussianImage q) := by
  rw [monsterNortonUTwoGaussianImage, xiSpinOperator_central_mul]
  exact xiGrayGaussian_conjugation _ _ _
    (fun a => monsterNortonUTwoGaussianTranslation_spin_swap a q)

/-- Invertibility is provided by the actual Gaussian involution. -/
noncomputable def monsterNortonUTwoGaussianEquiv : SpinSpace ≃ₗ[ℝ] SpinSpace :=
  LinearEquiv.ofInvolutive monsterNortonUTwoGaussian (fun f =>
    congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f) monsterNortonUTwoGaussian_square)

/-- The real spin operator is an actual orthogonal normalizer of the genuine Q image. -/
noncomputable def monsterNortonUTwoGaussianHolomorph : SpinHolomorph :=
  ⟨monsterNortonUTwoGaussianEquiv,
    xiSpinImage_normalizer_of_involution _
      (by
        apply LinearEquiv.ext
        intro f
        exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f)
          monsterNortonUTwoGaussian_square)
      monsterNortonUTwoGaussianImage (fun q => by
        apply LinearEquiv.ext
        intro f
        exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f)
          (monsterNortonUTwoGaussian_conjugation q)),
    monsterNortonUTwoGaussian_pairing⟩

/-- Normalizer conjugation has exactly the stated full coordinate image. -/
theorem monsterNortonUTwoGaussianHolomorph_conjugation (q : Q) :
    spinConjugation monsterNortonUTwoGaussianHolomorph q =
      monsterNortonUTwoGaussianImage q := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  have hs : monsterNortonUTwoGaussianEquiv * monsterNortonUTwoGaussianEquiv = 1 := by
    apply LinearEquiv.ext
    intro f
    exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f)
      monsterNortonUTwoGaussian_square
  have hi : monsterNortonUTwoGaussianEquiv⁻¹ = monsterNortonUTwoGaussianEquiv :=
    inv_eq_of_mul_eq_one_right hs
  change monsterNortonUTwoGaussianEquiv * spinRepresentation q *
    monsterNortonUTwoGaussianEquiv⁻¹ = spinRepresentation (monsterNortonUTwoGaussianImage q)
  rw [hi]
  apply LinearEquiv.toLinearMap_injective
  exact monsterNortonUTwoGaussian_conjugation q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
