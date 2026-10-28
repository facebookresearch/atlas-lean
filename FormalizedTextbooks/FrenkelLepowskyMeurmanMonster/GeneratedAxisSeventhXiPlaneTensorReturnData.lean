/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianFastAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorPackedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorFourColumns

/-! Small exact expressions for both sides of the full original tensor return. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The full original corrected spin numerator on one genuine tensor column. -/
def generatedSeventhXiPlaneTensorReturnLeft (d : Fin 4096) (j : Fin 24) : ℤ :=
  generatedSeventhXiPlaneGaussianFast (fun x => generatedSeventhXiPlaneTensorPacked x j) d

/-- The four nonzero row addresses of each original spatial column. -/
def generatedSeventhXiPlaneTensorFourTransposeColumn : Fin 24 → Fin 4 → Fin 24 :=
  ![
    ![0, 6, 9, 20],
    ![1, 5, 11, 22],
    ![2, 7, 10, 23],
    ![3, 4, 8, 21],
    ![3, 4, 8, 21],
    ![1, 5, 11, 22],
    ![0, 6, 9, 20],
    ![2, 7, 10, 23],
    ![3, 4, 8, 21],
    ![0, 6, 9, 20],
    ![2, 7, 10, 23],
    ![1, 5, 11, 22],
    ![12, 13, 14, 18],
    ![12, 13, 14, 18],
    ![12, 13, 14, 18],
    ![15, 16, 17, 19],
    ![15, 16, 17, 19],
    ![15, 16, 17, 19],
    ![12, 13, 14, 18],
    ![15, 16, 17, 19],
    ![0, 6, 9, 20],
    ![3, 4, 8, 21],
    ![1, 5, 11, 22],
    ![2, 7, 10, 23]
  ]

/-- The complete original integral signs in those four spatial column entries. -/
def generatedSeventhXiPlaneTensorFourTransposeSign : Fin 24 → Fin 4 → ℤ :=
  ![
    ![-1, -1, -1, -1],
    ![1, 1, -1, -1],
    ![1, -1, -1, 1],
    ![1, -1, 1, -1],
    ![-1, 1, 1, -1],
    ![-1, -1, -1, -1],
    ![1, 1, -1, -1],
    ![-1, 1, -1, 1],
    ![-1, -1, -1, -1],
    ![1, -1, 1, -1],
    ![-1, -1, 1, 1],
    ![-1, 1, 1, -1],
    ![1, 1, -1, -1],
    ![-1, -1, -1, -1],
    ![-1, 1, 1, -1],
    ![-1, -1, -1, -1],
    ![1, 1, -1, -1],
    ![1, -1, 1, -1],
    ![-1, 1, -1, 1],
    ![1, -1, -1, 1],
    ![1, -1, -1, 1],
    ![-1, -1, 1, 1],
    ![-1, 1, -1, 1],
    ![-1, -1, -1, -1]
  ]

/-- The four actual spatial terms required by the original tensor return. -/
def generatedSeventhXiPlaneTensorReturnRight (d : Fin 4096) (j : Fin 24) : ℤ :=
  4 * ∑ k : Fin 4, generatedSeventhXiPlaneTensorFourTransposeSign j k *
    generatedSeventhXiPlaneTensorPacked d (generatedSeventhXiPlaneTensorFourTransposeColumn j k)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every original matrix entry is retained; no symmetry of the Xi matrix is assumed.
/-- The four column entries equal every entry of the genuine spatial numerator. -/
theorem generatedSeventhXiPlaneTensorFourTranspose_certificate : ∀ i j : Fin 24,
    generatedSeventhXiPlaneTensorSpatialNumerator i j =
      ∑ k : Fin 4, generatedSeventhXiPlaneTensorFourTransposeSign j k *
        (if i = generatedSeventhXiPlaneTensorFourTransposeColumn j k then 1 else 0) := by
  decide +kernel

/-- The full original spatial column action equals its four genuine nonzero entries. -/
theorem generatedSeventhXiPlaneTensorFourTranspose_sum (j : Fin 24) (v : Fin 24 → ℤ) :
    (∑ i : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j * v i) =
      ∑ k : Fin 4, generatedSeventhXiPlaneTensorFourTransposeSign j k *
        v (generatedSeventhXiPlaneTensorFourTransposeColumn j k) := by
  simp_rw [generatedSeventhXiPlaneTensorFourTranspose_certificate, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

/-- The four spatial terms equal the entire original twenty-four-column sum. -/
theorem generatedSeventhXiPlaneTensorReturnRight_actual (d : Fin 4096) (j : Fin 24) :
    generatedSeventhXiPlaneTensorReturnRight d j =
      4 * ∑ i : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
        generatedSeventhXiPlaneTensorPacked d i :=
  congrArg (fun n : ℤ => 4 * n)
    (generatedSeventhXiPlaneTensorFourTranspose_sum j (generatedSeventhXiPlaneTensorPacked d)).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
