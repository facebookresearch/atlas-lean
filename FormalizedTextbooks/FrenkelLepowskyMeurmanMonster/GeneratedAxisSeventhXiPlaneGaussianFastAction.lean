/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianParityCache

/-! Cached parity evaluates the entire original corrected spin operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The exact original Gaussian numerator using the fully checked phase table. -/
def generatedSeventhXiPlaneGaussianFast (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun d => ∑ a : Fin 64, generatedSeventhXiPlaneGaussianGraySign a *
    generatedSeventhXiGaussianFastPhase a d *
    generatedSeventhXiGaussianPackedGamma
      (monsterNortonBitXor d (generatedSeventhXiGaussianPackedShift a)) *
    v (monsterNortonBitXor d (generatedSeventhXiGaussianPackedShift a))

/-- Every cached operator coefficient retains the original source Pauli phase. -/
theorem generatedSeventhXiPlaneGaussianFast_eq (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneGaussianFast v = generatedSeventhXiPlaneGaussianPacked v := by
  funext d
  apply Finset.sum_congr rfl
  intro a _
  rw [generatedSeventhXiGaussianFastPhase_actual]

/-- The cached phase evaluator is the complete original corrected spin operator. -/
theorem generatedSeventhXiPlaneGaussianFast_actual (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneIntegerSpin v = generatedSeventhXiPlaneGaussianFast v := by
  rw [generatedSeventhXiPlaneGaussianFast_eq]
  exact generatedSeventhXiPlaneGaussianPacked_actual v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
