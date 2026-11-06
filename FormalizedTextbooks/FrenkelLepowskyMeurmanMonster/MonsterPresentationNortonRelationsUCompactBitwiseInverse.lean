/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A propositionally bound fast coordinate formula for the actual inverse Norton numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseLabels

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact inner label of one inverse compact Gaussian summand, evaluated by bitwise rows. -/
def monsterNortonUCompactBitInner (n : Fin 4096) (a : Fin 64) : Fin 4096 :=
  monsterNortonUCompactBitPermutation 0
    (monsterNortonBitXor (monsterNortonUCompactBitPermutation 1 n) (monsterNortonBitGrayLabel a))

/-- A sixty-four-term bitwise evaluator for the same actual integer inverse numerator. -/
def monsterNortonUCompactBitInverseNumerator (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => monsterNortonUCompactBitDiagonal 1 n * ∑ a : Fin 64,
    xiGraySign (monsterNortonGrayCoefficients a) *
      monsterNortonUCompactBitDiagonal 0 (monsterNortonUCompactBitInner n a) *
      monsterNortonUCompactBitInversePhase (monsterNortonUCompactBitInner n a) *
      v (monsterNortonBitXor (monsterNortonUCompactBitInner n a) 1024)

private theorem gaussian_sum64 (v : NortonUIntegerVector) (n : Fin 4096) :
    nortonUIntegerG v n = ∑ a : Fin 64, xiGraySign (monsterNortonGrayCoefficients a) *
      v (nortonUIntegerLabel (golayLabelCoefficients n +
        xiGrayCode (monsterNortonGrayCoefficients a))) := by
  exact (Equiv.sum_comp monsterNortonGrayEquiv (fun g : XiGrayIndex =>
    xiGraySign g * v (nortonUIntegerLabel (golayLabelCoefficients n + xiGrayCode g)))).symm

/-- The bitwise evaluator is exactly the actual inverse compact operator on every integer vector. -/
theorem monsterNortonUCompactBitInverseNumerator_actual (v : NortonUIntegerVector) :
    monsterNortonUCompactInverseNumerator v = monsterNortonUCompactBitInverseNumerator v := by
  funext n
  simp only [monsterNortonUCompactInverseNumerator, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, LinearEquiv.symm_symm, gaussian_sum64]
  rw [monsterNortonUCompactBitDiagonal_actual_1,
    monsterNortonUCompactBitPermutation_actual_1]
  unfold monsterNortonUCompactBitInverseNumerator
  apply congrArg (fun z : ℤ => monsterNortonUCompactBitDiagonal 1 n * z)
  apply Finset.sum_congr rfl
  intro a _
  have hg : nortonUIntegerLabel
      (golayLabelCoefficients (monsterNortonUCompactBitPermutation 1 n) +
        xiGrayCode (monsterNortonGrayCoefficients a)) =
          monsterNortonBitXor (monsterNortonUCompactBitPermutation 1 n)
            (monsterNortonBitGrayLabel a) := by
    rw [monsterNortonBitXor_label, nortonUIntegerLabel_coeff, monsterNortonBitGrayLabel_actual]
  rw [hg, monsterNortonUCompactBitPermutation_actual_0]
  simp only [nortonUIntegerQ]
  rw [monsterNortonUCompactBitDiagonal_actual_0, monsterNortonUCompactBitInversePhase_actual,
    monsterNortonBitXor_label, nortonUIntegerLabel_coeff,
    monsterNortonUCompactBitInverseTranslation_actual]
  simp only [monsterNortonUCompactBitInner]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
