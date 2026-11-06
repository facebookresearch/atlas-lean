/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianBitData

/-! The whole original corrected spin numerator using sixty-four verified signed shifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original full Gaussian numerator, evaluated by the genuine Pauli labels and phases. -/
def generatedSeventhXiPlaneGaussianBit (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun d => ∑ a : Fin 64, generatedSeventhXiPlaneGaussianGraySign a *
    generatedSeventhXiPlaneGaussianBitPhase a d *
    generatedSeventhXiPlaneConjugateGammaBit
      (monsterNortonBitXor d (generatedSeventhXiPlaneGaussianTranslationLabel a)) *
    v (monsterNortonBitXor d (generatedSeventhXiPlaneGaussianTranslationLabel a))

set_option maxHeartbeats 1000000 in
-- Reindex the original sixty-four-term operator while preserving all actual phases.
/-- All sixty-four signed shifts equal the original complete corrected integer spin operator. -/
theorem generatedSeventhXiPlaneGaussianBit_actual (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneIntegerSpin v = generatedSeventhXiPlaneGaussianBit v := by
  rw [generatedSeventhXiPlanePauliGaussian_actual]
  funext d
  simp only [generatedSeventhXiPlanePauliGaussian, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have hs := (Equiv.sum_comp monsterNortonGrayEquiv (fun a : XiGrayIndex =>
    xiGraySign a * nortonUIntegerQ (generatedSeventhXiPlaneGaussianQ a)
      (fun x => generatedSeventhXiPlaneConjugateGamma x * v x) d)).symm
  refine hs.trans ?_
  unfold generatedSeventhXiPlaneGaussianBit
  apply Finset.sum_congr rfl
  intro a _
  have he : monsterNortonGrayEquiv a = monsterNortonGrayCoefficients a := rfl
  rw [he, ← generatedSeventhXiPlaneGaussianQLiteral_actual a]
  simp only [nortonUIntegerQ, generatedSeventhXiPlaneGaussian_bit_phase,
    generatedSeventhXiPlaneGaussian_translation, monsterNortonBitXor_label,
    nortonUIntegerLabel_coeff, generatedSeventhXiPlaneConjugateGammaBit_actual,
    generatedSeventhXiPlaneGaussian_gray_sign]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
