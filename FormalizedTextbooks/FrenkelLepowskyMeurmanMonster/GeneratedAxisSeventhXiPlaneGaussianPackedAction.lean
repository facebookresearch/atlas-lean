/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianPackedCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianBitAction

/-! Packed tables evaluate the complete original corrected spin operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The verified original Gaussian numerator with compact phase and shift tables. -/
def generatedSeventhXiPlaneGaussianPacked (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun d => ∑ a : Fin 64, generatedSeventhXiPlaneGaussianGraySign a *
    generatedSeventhXiGaussianPackedPhase a d *
    generatedSeventhXiGaussianPackedGamma
      (monsterNortonBitXor d (generatedSeventhXiGaussianPackedShift a)) *
    v (monsterNortonBitXor d (generatedSeventhXiGaussianPackedShift a))

/-- Packed evaluation retains every genuine Pauli shift and its complete source phase. -/
theorem generatedSeventhXiPlaneGaussianPacked_eq (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneGaussianPacked v = generatedSeventhXiPlaneGaussianBit v := by
  funext d
  apply Finset.sum_congr rfl
  intro a _
  simp only [generatedSeventhXiGaussianPacked_phase,
    (generatedSeventhXiGaussianPacked_pauli a).1,
    generatedSeventhXiGaussianPacked_gamma]

/-- The packed evaluator is the entire original corrected integer spin operator. -/
theorem generatedSeventhXiPlaneGaussianPacked_actual (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneIntegerSpin v = generatedSeventhXiPlaneGaussianPacked v := by
  rw [generatedSeventhXiPlaneGaussianPacked_eq]
  exact generatedSeventhXiPlaneGaussianBit_actual v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
