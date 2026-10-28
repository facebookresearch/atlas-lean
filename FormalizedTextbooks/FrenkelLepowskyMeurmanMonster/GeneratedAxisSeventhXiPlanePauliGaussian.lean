/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneIntegerSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

/-! The original corrected Gaussian as a finite sum of genuine extraspecial operators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem linear_mul_apply (a b : SpinSpace ≃ₗ[ℝ] SpinSpace) (v : SpinSpace) :
    (a * b) v = a (b v) := rfl

private theorem linear_inv_apply (a : SpinSpace ≃ₗ[ℝ] SpinSpace) (v : SpinSpace) :
    a⁻¹ v = a.symm v := rfl

private theorem compact_intertwines (q : Q) (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneIntegerCompact (nortonUIntegerQ q v) =
      nortonUIntegerQ (generatedSeventhXiPlaneCompactImage q)
        (generatedSeventhXiPlaneIntegerCompact v) := by
  apply monsterNortonUIntegerEmbed_injective
  rw [← generatedSeventhXiPlane_integer_compact_embed, ← nortonUIntegerQ_embed,
    ← nortonUIntegerQ_embed, ← generatedSeventhXiPlane_integer_compact_embed]
  have h := congrArg (fun e : SpinSpace ≃ₗ[ℝ] SpinSpace =>
      e (generatedSeventhXiPlaneCompactSpin.val (nortonUIntegerEmbed v)))
    (spinConjugation_representation generatedSeventhXiPlaneCompactSpin q)
  simp only [generatedSeventhXiPlaneCompactSpin_conjugation,
    linear_mul_apply, linear_inv_apply, LinearEquiv.symm_apply_apply] at h
  exact h.symm

private theorem q_mul (q r : Q) (v : NortonUIntegerVector) :
    nortonUIntegerQ (q * r) v = nortonUIntegerQ q (nortonUIntegerQ r v) := by
  apply monsterNortonUIntegerEmbed_injective
  rw [← nortonUIntegerQ_embed, ← nortonUIntegerQ_embed, ← nortonUIntegerQ_embed,
    map_mul]
  rfl

private theorem integral_sign_square (c : ZMod 2) :
    nortonUIntegerSign c * nortonUIntegerSign c = 1 := by
  unfold nortonUIntegerSign
  by_cases hc : c = 0 <;> simp [hc]

/-- The complete diagonal after conjugating the original cocode Gaussian by the source word. -/
def generatedSeventhXiPlaneConjugateGamma (d : Fin 4096) : ℤ :=
  nortonUIntegerGammaSign
    (generatedSeventhXiPlaneCode.symm (golayLabelCoefficients d))

private theorem compact_gamma (v : NortonUIntegerVector) (d : Fin 4096) :
    generatedSeventhXiPlaneIntegerCompact
      (nortonUIntegerGamma (generatedSeventhXiPlaneIntegerCompactInverse v)) d =
        generatedSeventhXiPlaneConjugateGamma d * v d := by
  simp only [generatedSeventhXiPlaneIntegerCompact, nortonUIntegerGamma,
    generatedSeventhXiPlaneIntegerCompactInverse, nortonUIntegerLabel_inverse,
    LinearEquiv.apply_symm_apply, nortonUIntegerLabel_coeff,
    generatedSeventhXiPlaneConjugateGamma]
  have hs := integral_sign_square (monsterMonomialQuadratic generatedSeventhXiPlanePhase
    (generatedSeventhXiPlaneCode.symm (golayLabelCoefficients d)))
  linear_combination
    (nortonUIntegerGammaSign
      (generatedSeventhXiPlaneCode.symm (golayLabelCoefficients d)) * v d) * hs

private theorem gaussian_sum (v : NortonUIntegerVector) :
    nortonUIntegerG v = ∑ a : XiGrayIndex,
      xiGraySign a • nortonUIntegerQ (xiGrayTranslation (ofAdd a)) v := by
  funext d
  have hc (a : XiGrayIndex) : toAdd (xiGrayTranslation (ofAdd a)).coeff = 0 := rfl
  simp only [nortonUIntegerG, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerQ, spinPhase, xiGrayTranslation_translation,
    xiGrayTranslation_modulation, spinDot_zero_left, hc, zero_add,
    nortonUIntegerSign, ite_true, one_mul]

private theorem compact_sum (v : XiGrayIndex → NortonUIntegerVector) :
    generatedSeventhXiPlaneIntegerCompact (∑ a, xiGraySign a • v a) =
      ∑ a, xiGraySign a • generatedSeventhXiPlaneIntegerCompact (v a) := by
  funext d
  simp only [generatedSeventhXiPlaneIntegerCompact, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem q_sum (q : Q) (v : XiGrayIndex → NortonUIntegerVector) :
    nortonUIntegerQ q (∑ a, xiGraySign a • v a) =
      ∑ a, xiGraySign a • nortonUIntegerQ q (v a) := by
  funext d
  simp only [nortonUIntegerQ, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Each summand is an actual full-phase extraspecial element of the corrected Gaussian. -/
def generatedSeventhXiPlaneGaussianQ (a : XiGrayIndex) : Q :=
  generatedSeventhXiPlaneCorrection *
    generatedSeventhXiPlaneCompactImage (xiGrayTranslation (ofAdd a))

/-- The original numerator as sixty-four genuine Q operators after its conjugated diagonal. -/
def generatedSeventhXiPlanePauliGaussian (v : NortonUIntegerVector) : NortonUIntegerVector :=
  ∑ a : XiGrayIndex, xiGraySign a • nortonUIntegerQ (generatedSeventhXiPlaneGaussianQ a)
    (fun d => generatedSeventhXiPlaneConjugateGamma d * v d)

/-- The Pauli sum is exactly the original corrected Xi numerator on every integer vector. -/
theorem generatedSeventhXiPlanePauliGaussian_actual (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneIntegerSpin v = generatedSeventhXiPlanePauliGaussian v := by
  have hg : generatedSeventhXiPlaneIntegerCompact
      (nortonUIntegerGamma (generatedSeventhXiPlaneIntegerCompactInverse v)) =
        (fun d => generatedSeventhXiPlaneConjugateGamma d * v d) := by
    funext d
    exact compact_gamma v d
  simp only [generatedSeventhXiPlaneIntegerSpin, nortonUIntegerXi,
    gaussian_sum, compact_sum, q_sum]
  simp_rw [compact_intertwines, hg, ← q_mul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
