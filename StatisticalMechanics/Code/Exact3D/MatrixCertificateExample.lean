/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FixedPointSkeleton








namespace StatMech
namespace Exact3D

namespace MatrixCertificateExample


noncomputable def stableMatrix : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : ℝ) / 2
  | ⟨1, _⟩, ⟨1, _⟩ => (1 : ℝ) / 3
  | _, _ => 0


def stableIntervals : RatInterval.IntervalMatrix 2 2
  | ⟨0, _⟩, ⟨0, _⟩ => RatInterval.point (1 / 2)
  | ⟨1, _⟩, ⟨1, _⟩ => RatInterval.point (1 / 3)
  | _, _ => RatInterval.point 0


def stableMatrixQ : Fin 2 → Fin 2 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => 1 / 2
  | ⟨1, _⟩, ⟨1, _⟩ => 1 / 3
  | _, _ => 0



theorem stableIntervals_eq_pointMatrix :
    stableIntervals = RatInterval.pointMatrix stableMatrixQ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stableIntervals, stableMatrixQ, RatInterval.pointMatrix,
      RatInterval.point]


theorem stableMatrix_eq_rational :
    stableMatrix = fun i j => (stableMatrixQ i j : ℝ) := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [stableMatrix, stableMatrixQ]


theorem stableMatrix_mem_intervals :
    RatInterval.MatrixMem stableMatrix stableIntervals := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stableMatrix, stableIntervals, RatInterval.point, RatInterval.MemR]



theorem stableMatrix_mem_pointMatrix :
    RatInterval.MatrixMem stableMatrix (RatInterval.pointMatrix stableMatrixQ) := by
  rw [stableMatrix_eq_rational]
  exact RatInterval.pointMatrix_memR stableMatrixQ


def stableCenterQ : Fin 2 → ℚ :=
  fun _ => 0



theorem stableRationalResidual_memQ :
    RatInterval.VectorMemQ
      (fun i => (∑ j, stableMatrixQ i j * stableCenterQ j) - stableCenterQ i)
      (RatInterval.matrixVectorResidual (RatInterval.pointMatrix stableMatrixQ)
        (RatInterval.pointVector stableCenterQ)) :=
  RatInterval.matrixVectorResidual_memQ
    (RatInterval.pointMatrix_memQ stableMatrixQ)
    (RatInterval.pointVector_memQ stableCenterQ)



theorem stableRationalResidual_absSum_zero :
    RatInterval.VectorAbsSum
      (RatInterval.matrixVectorResidual (RatInterval.pointMatrix stableMatrixQ)
        (RatInterval.pointVector stableCenterQ)) = 0 := by
  norm_num [RatInterval.VectorAbsSum, RatInterval.matrixVectorResidual,
    RatInterval.matrixVectorMul, RatInterval.pointMatrix, RatInterval.pointVector,
    RatInterval.finsetSum, RatInterval.vectorSub, RatInterval.sub,
    RatInterval.add, RatInterval.neg, RatInterval.mul, RatInterval.point,
    RatInterval.absUpper, stableMatrixQ, stableCenterQ]


def stableRowSumContraction :
    RatInterval.RowSumContraction stableIntervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i <;>
      norm_num [RatInterval.MatrixAbsRowSum, stableIntervals,
        RatInterval.point, RatInterval.absUpper]



def stablePointMatrixRowSumContraction :
    RatInterval.RowSumContraction (RatInterval.pointMatrix stableMatrixQ) :=
  RatInterval.rowSumContraction_of_pointMatrix stableMatrixQ
    (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℚ) < 1) (by
      intro i
      fin_cases i <;> norm_num [stableMatrixQ])


def stableColumnSumContraction :
    RatInterval.ColumnSumContraction stableIntervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  col_bound := by
    intro j
    fin_cases j <;>
      norm_num [RatInterval.MatrixAbsColSum, stableIntervals,
        RatInterval.point, RatInterval.absUpper]



def stablePointMatrixColumnSumContraction :
    RatInterval.ColumnSumContraction (RatInterval.pointMatrix stableMatrixQ) :=
  RatInterval.columnSumContraction_of_pointMatrix stableMatrixQ
    (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℚ) < 1) (by
      intro j
      fin_cases j <;> norm_num [stableMatrixQ])


theorem stableMatrix_map_zero :
    (fun i => RatInterval.matVec stableMatrix (0 : Fin 2 → ℝ) i) = 0 := by
  funext i
  simp [RatInterval.matVec]



noncomputable def stableColumnClosedBallCertificate :
    FiniteContraction.ClosedBallContractionCertificate
      (fun x i => RatInterval.matVec stableMatrix x i) :=
  FiniteContraction.closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter
    stablePointMatrixColumnSumContraction stableMatrix_mem_pointMatrix
    stableCenterQ (radius := 0) (by norm_num) (by
      rw [stableRationalResidual_absSum_zero]
      norm_num)



theorem stableColumnClosedBallCertificate_exists_fixedPoint :
    ∃ p : Fin 2 → ℝ,
      (fun x i => RatInterval.matVec stableMatrix x i) p = p ∧
        FiniteContraction.ClosedBall
          stableColumnClosedBallCertificate.center
          stableColumnClosedBallCertificate.radius p :=
  stableColumnClosedBallCertificate.exists_fixedPoint



theorem stableColumnClosedBallCertificate_fixedPoint_eq_zero :
    stableColumnClosedBallCertificate.fixedPoint = 0 :=
  stableColumnClosedBallCertificate.fixedPoint_unique
    stableColumnClosedBallCertificate.fixedPoint_isFixed stableMatrix_map_zero


theorem stableMatrix_apply_bound (x : Fin 2 → ℝ) (i : Fin 2) :
    |RatInterval.matVec stableMatrix x i| ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stableRowSumContraction] using
    stableRowSumContraction.apply_bound stableMatrix_mem_intervals x i



theorem stablePointMatrix_apply_bound (x : Fin 2 → ℝ) (i : Fin 2) :
    |RatInterval.matVec stableMatrix x i| ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stablePointMatrixRowSumContraction,
    RatInterval.rowSumContraction_of_pointMatrix] using
    stablePointMatrixRowSumContraction.apply_bound stableMatrix_mem_pointMatrix x i


theorem stableMatrix_apply_l1_bound (x : Fin 2 → ℝ) :
    RatInterval.supNormVec (fun i => RatInterval.matVec stableMatrix x i) ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stableColumnSumContraction] using
    stableColumnSumContraction.apply_l1_bound stableMatrix_mem_intervals x



theorem stablePointMatrix_apply_l1_bound (x : Fin 2 → ℝ) :
    RatInterval.supNormVec (fun i => RatInterval.matVec stableMatrix x i) ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [stablePointMatrixColumnSumContraction,
    RatInterval.columnSumContraction_of_pointMatrix] using
    stablePointMatrixColumnSumContraction.apply_l1_bound
      stableMatrix_mem_pointMatrix x



theorem stableIntervals_offDiagAbsRowSum_zero (i : Fin 2) :
    RatInterval.IntervalOffDiagAbsRowSum stableIntervals i = 0 := by
  fin_cases i <;>
    norm_num [RatInterval.IntervalOffDiagAbsRowSum, stableIntervals,
      RatInterval.point, RatInterval.absUpper]




theorem stableMatrix_gershgorin_zero_radius
    (x : Fin 2 → ℝ) (lam : ℝ) (i : Fin 2)
    (heig_i : RatInterval.matVec stableMatrix x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |lam - stableMatrix i i| ≤ 0 := by
  have h := RatInterval.gershgorin_interval_row_bound_of_pivot
    stableMatrix_mem_intervals x lam i heig_i hxi hpivot
  simpa [stableIntervals_offDiagAbsRowSum_zero i] using h



theorem stableMatrix_eigenvalue_gershgorin_zero_radius
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, |lam - stableMatrix i i| ≤ 0 := by
  rcases RatInterval.gershgorin_interval_bound_of_eigenvector
      stableMatrix_mem_intervals x lam heig hnonzero with ⟨i, hi⟩
  exact ⟨i, by simpa [stableIntervals_offDiagAbsRowSum_zero i] using hi⟩



theorem stableMatrix_eigenvalue_mem_interval_gershgorin_disk
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, RatInterval.IntervalGershgorinRowDisk stableIntervals lam i :=
  RatInterval.exists_intervalGershgorinRowDisk_of_eigenvector
    stableMatrix_mem_intervals x lam heig hnonzero



theorem stableMatrix_eigenvalue_mem_interval_gershgorin_rowInterval
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i,
      (RatInterval.IntervalGershgorinRowInterval stableIntervals i).MemR lam :=
  RatInterval.exists_mem_intervalGershgorinRowInterval_of_eigenvector
    stableMatrix_mem_intervals x lam heig hnonzero



theorem stableMatrix_eigenvalue_eq_half_or_third
    (x : Fin 2 → ℝ) (lam : ℝ)
    (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    lam = (1 : ℝ) / 2 ∨ lam = (1 : ℝ) / 3 := by
  rcases stableMatrix_eigenvalue_gershgorin_zero_radius x lam heig hnonzero
    with ⟨i, hi⟩
  have hzero : |lam - stableMatrix i i| = 0 :=
    le_antisymm hi (abs_nonneg _)
  have hdiag : lam = stableMatrix i i :=
    sub_eq_zero.mp (abs_eq_zero.mp hzero)
  fin_cases i
  · left
    norm_num [stableMatrix] at hdiag
    exact hdiag
  · right
    norm_num [stableMatrix] at hdiag
    exact hdiag


theorem stableIntervals_endpointSeparated_zero (i : Fin 2) :
    RatInterval.IntervalGershgorinRowEndpointSeparated stableIntervals 0 i := by
  fin_cases i <;>
    norm_num [RatInterval.IntervalGershgorinRowEndpointSeparated,
      RatInterval.IntervalOffDiagAbsRowSum, stableIntervals,
      RatInterval.point, RatInterval.absUpper]



theorem stableMatrix_not_exists_zero_eigenvector :
    ¬ ∃ x : Fin 2 → ℝ,
      (∀ i, RatInterval.matVec stableMatrix x i = 0 * x i) ∧ ∃ i, x i ≠ 0 :=
  RatInterval.not_exists_eigenvector_of_interval_gershgorin_endpoint_separation
    stableMatrix_mem_intervals 0 stableIntervals_endpointSeparated_zero



theorem stableIntervals_endpointSeparatedOnIcc_near_zero (i : Fin 2) :
    RatInterval.IntervalGershgorinRowEndpointSeparatedOnIcc stableIntervals
      (-(1 : ℝ) / 10) ((1 : ℝ) / 10) i := by
  fin_cases i <;>
    norm_num [RatInterval.IntervalGershgorinRowEndpointSeparatedOnIcc,
      RatInterval.IntervalOffDiagAbsRowSum, stableIntervals,
      RatInterval.point, RatInterval.absUpper]



theorem stableMatrix_not_exists_eigenvector_with_eigenvalue_near_zero :
    ¬ ∃ lam : ℝ, lam ∈ Set.Icc (-(1 : ℝ) / 10) ((1 : ℝ) / 10) ∧
      ∃ x : Fin 2 → ℝ,
        (∀ i, RatInterval.matVec stableMatrix x i = lam * x i) ∧
          ∃ i, x i ≠ 0 :=
  RatInterval.not_exists_eigenvector_in_Icc_of_endpoint_separation
    stableMatrix_mem_intervals
    (-(1 : ℝ) / 10) ((1 : ℝ) / 10)
    stableIntervals_endpointSeparatedOnIcc_near_zero

end MatrixCertificateExample

end Exact3D
end StatMech
