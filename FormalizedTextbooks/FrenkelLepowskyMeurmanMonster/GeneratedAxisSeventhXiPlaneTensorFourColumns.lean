/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneIntegerTensor

/-! The complete original spatial matrix acts through exactly four signed columns per row. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true

/-- The four nonzero physical columns of each original conjugated Xi row. -/
def generatedSeventhXiPlaneTensorFourColumn : Fin 24 → Fin 4 → Fin 24 :=
  ![
    ![0, 20, 6, 9],
    ![5, 22, 11, 1],
    ![23, 2, 10, 7],
    ![8, 21, 3, 4],
    ![8, 21, 3, 4],
    ![5, 22, 11, 1],
    ![0, 20, 6, 9],
    ![23, 2, 10, 7],
    ![8, 21, 3, 4],
    ![0, 20, 6, 9],
    ![23, 2, 10, 7],
    ![5, 22, 11, 1],
    ![13, 18, 14, 12],
    ![13, 18, 14, 12],
    ![13, 18, 14, 12],
    ![15, 19, 17, 16],
    ![15, 19, 17, 16],
    ![15, 19, 17, 16],
    ![13, 18, 14, 12],
    ![15, 19, 17, 16],
    ![0, 20, 6, 9],
    ![8, 21, 3, 4],
    ![5, 22, 11, 1],
    ![23, 2, 10, 7]
  ]

/-- Their actual integral signs, before dividing the spatial matrix by two. -/
def generatedSeventhXiPlaneTensorFourSign : Fin 24 → Fin 4 → ℤ :=
  ![
    ![-1, 1, 1, 1],
    ![-1, -1, -1, 1],
    ![-1, 1, -1, -1],
    ![-1, -1, 1, -1],
    ![-1, -1, -1, 1],
    ![-1, 1, 1, 1],
    ![-1, -1, 1, -1],
    ![-1, -1, -1, 1],
    ![-1, 1, 1, 1],
    ![-1, -1, -1, 1],
    ![-1, -1, 1, -1],
    ![-1, -1, 1, -1],
    ![-1, -1, -1, 1],
    ![-1, 1, 1, 1],
    ![-1, -1, 1, -1],
    ![-1, 1, 1, 1],
    ![-1, -1, -1, 1],
    ![-1, -1, 1, -1],
    ![-1, 1, -1, -1],
    ![-1, 1, -1, -1],
    ![-1, 1, -1, -1],
    ![-1, 1, -1, -1],
    ![-1, 1, -1, -1],
    ![-1, 1, 1, 1]
  ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every one of the original 576 matrix entries is verified.
/-- These four signed columns are exactly every entry of the genuine spatial numerator. -/
theorem generatedSeventhXiPlaneTensorFour_certificate : ∀ i j : Fin 24,
    generatedSeventhXiPlaneTensorSpatialNumerator i j =
      ∑ k : Fin 4, generatedSeventhXiPlaneTensorFourSign i k *
        (if j = generatedSeventhXiPlaneTensorFourColumn i k then 1 else 0) := by
  decide +kernel

/-- The full twenty-four-column integer action equals these four original signed columns. -/
theorem generatedSeventhXiPlaneTensorFour_sum (i : Fin 24) (v : Fin 24 → ℤ) :
    (∑ j : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j * v j) =
      ∑ k : Fin 4, generatedSeventhXiPlaneTensorFourSign i k *
        v (generatedSeventhXiPlaneTensorFourColumn i k) := by
  simp_rw [generatedSeventhXiPlaneTensorFour_certificate, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
