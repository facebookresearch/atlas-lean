/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Sixteen actual real-coordinate rows of the rank-four Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoGaussianAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The retained quadratic phase after summing both omitted directions. -/
def monsterNortonUTwoGaussianQuadratic (b : Fin 16) : ZMod 2 :=
  if monsterNortonUTwoGaussianSign b = 1 then 0 else 1

/-- The finite integer signs are precisely the actual real quadratic phases. -/
theorem monsterNortonUTwoGaussianSign_real (b : Fin 16) :
    (monsterNortonUTwoGaussianSign b : ℝ) =
      qSign (monsterNortonUTwoGaussianQuadratic b) := by
  fin_cases b <;> simp [monsterNortonUTwoGaussianSign, monsterNortonUTwoGaussianQuadratic, qSign]

private theorem weighted_sum_real (f : Fin 16 → ℝ) :
    (∑ a : XiGrayIndex, (xiGraySign a : ℝ) * f (monsterNortonUTwoGaussianLabel a)) =
      2 * ∑ b : Fin 16, (monsterNortonUTwoGaussianSign b : ℝ) * f b := by
  classical
  have hc (b : Fin 16) : (∑ a : XiGrayIndex,
      if monsterNortonUTwoGaussianLabel a = b then (xiGraySign a : ℝ) else 0) =
        2 * (monsterNortonUTwoGaussianSign b : ℝ) := by
    have h := monsterNortonUTwoGaussian_coefficient b
    exact_mod_cast h
  calc
    _ = ∑ a : XiGrayIndex, ∑ b : Fin 16,
        if monsterNortonUTwoGaussianLabel a = b then (xiGraySign a : ℝ) * f b else 0 := by
      congr 1
      ext a
      simp
    _ = ∑ b : Fin 16, ∑ a : XiGrayIndex,
        if monsterNortonUTwoGaussianLabel a = b then (xiGraySign a : ℝ) * f b else 0 :=
      Finset.sum_comm
    _ = ∑ b : Fin 16, (∑ a : XiGrayIndex,
        if monsterNortonUTwoGaussianLabel a = b then (xiGraySign a : ℝ) else 0) * f b := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    _ = 2 * ∑ b : Fin 16, (monsterNortonUTwoGaussianSign b : ℝ) * f b := by
      simp only [hc, Finset.mul_sum, mul_assoc]

private theorem translation_apply (a : XiGrayIndex) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (monsterNortonUTwoGaussianTranslation (Multiplicative.ofAdd a)) f t =
      f (t + monsterNortonUTwoGaussianCode a) := by
  have ht : spinTranslation (monsterNortonUTwoGaussianTranslation
      (Multiplicative.ofAdd a)) = monsterNortonUTwoGaussianCode a := by
    funext i
    exact Fin.append_left _ _ i
  have hm : spinModulation (monsterNortonUTwoGaussianTranslation
      (Multiplicative.ofAdd a)) = 0 := by
    funext i
    exact Fin.append_right _ _ i
  rw [xiSpinOperator_apply, ht]
  simp only [spinPhase, hm]
  change qSign (0 + spinDot 0 t) * f (t + monsterNortonUTwoGaussianCode a) = _
  simp

/-- The actual real Gaussian has exactly sixteen translated coordinate terms. -/
theorem monsterNortonUTwoGaussian_apply (f : SpinSpace) (t : SpinIndex) :
    monsterNortonUTwoGaussian f t = (1 / 4 : ℝ) *
      ∑ b : Fin 16, qSign (monsterNortonUTwoGaussianQuadratic b) *
        f (t + golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel b)) := by
  simp only [monsterNortonUTwoGaussian, xiGrayGaussian, LinearMap.smul_apply,
    LinearMap.sum_apply, MonoidHom.comp_apply]
  simp only [xiSpinLinearRepresentation_operator, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, translation_apply, monsterNortonUTwoGaussianCode_label,
    ← xiGraySign_real]
  rw [weighted_sum_real (fun b =>
    f (t + golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel b)))]
  simp only [monsterNortonUTwoGaussianSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
