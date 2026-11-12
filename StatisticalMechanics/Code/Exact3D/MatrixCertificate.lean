/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Intervals









namespace StatMech
namespace Exact3D

namespace RatInterval




noncomputable def supNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, |x i|

theorem abs_coord_le_supNormVec {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ supNormVec x := by
  classical
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (by simp)

theorem supNormVec_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ supNormVec x := by
  classical
  exact Finset.sum_nonneg fun i _ => abs_nonneg (x i)



def matVec {m n : ℕ} (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j, A i j * x j


def affineMap {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  matVec A x i + b i



theorem matrixVectorMul_memR_matVec {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ} {I : IntervalMatrix m n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i) (matrixVectorMul I X) := by
  simpa [matVec] using matrixVectorMul_memR hA hx



theorem matrixVectorMulNonneg_memR_matVec {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i) (matrixVectorMulNonneg I X hI hX) := by
  simpa [matVec] using matrixVectorMulNonneg_memR hI hX hA hx


theorem matrixVectorResidual_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i - x i) (matrixVectorResidual I X) := by
  simpa [matVec] using matrixVectorResidual_memR hA hx



theorem matrixVectorResidual_memR_matVec_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (center : Fin n → ℚ) :
    VectorMem
      (fun i => matVec A (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorResidual I (pointVector center)) :=
  matrixVectorResidual_memR_matVec hA (pointVector_memR center)



theorem matrixVectorResidualNonneg_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i - x i)
      (matrixVectorResidualNonneg I X hI hX) := by
  simpa [matVec] using matrixVectorResidualNonneg_memR hI hX hA hx



theorem matrixVectorResidualNonneg_memR_matVec_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hI : MatrixNonnegative I) (hA : MatrixMem A I)
    (center : Fin n → ℚ) (hcenter : ∀ i, 0 ≤ center i) :
    VectorMem
      (fun i => matVec A (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorResidualNonneg I (pointVector center) hI
        (pointVector_nonnegative hcenter)) :=
  matrixVectorResidualNonneg_memR_matVec hI
    (pointVector_nonnegative hcenter) hA (pointVector_memR center)


theorem matrixVectorAffine_memR_affineMap {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i) (matrixVectorAffine I B X) := by
  simpa [affineMap, matVec] using matrixVectorAffine_memR hA hb hx



theorem matrixVectorAffineNonneg_memR_affineMap {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  simpa [affineMap, matVec] using
    matrixVectorAffineNonneg_memR hI hX hA hb hx


theorem matrixVectorAffineResidual_memR_affineMap {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i - x i)
      (matrixVectorAffineResidual I B X) := by
  simpa [affineMap, matVec] using matrixVectorAffineResidual_memR hA hb hx


theorem matrixVectorAffineResidual_memR_affineMap_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ}
    {I : IntervalMatrix n n} {B : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B)
    (center : Fin n → ℚ) :
    VectorMem
      (fun i =>
        affineMap A b (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorAffineResidual I B (pointVector center)) :=
  matrixVectorAffineResidual_memR_affineMap hA hb
    (pointVector_memR center)



theorem matrixVectorAffineResidualNonneg_memR_affineMap {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  simpa [affineMap, matVec] using
    matrixVectorAffineResidualNonneg_memR hI hX hA hb hx



theorem matrixVectorAffineResidualNonneg_memR_affineMap_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ}
    {I : IntervalMatrix n n} {B : IntervalVector n}
    (hI : MatrixNonnegative I) (hA : MatrixMem A I)
    (hb : VectorMem b B) (center : Fin n → ℚ)
    (hcenter : ∀ i, 0 ≤ center i) :
    VectorMem
      (fun i =>
        affineMap A b (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorAffineResidualNonneg I B (pointVector center) hI
        (pointVector_nonnegative hcenter)) :=
  matrixVectorAffineResidualNonneg_memR_affineMap hI
    (pointVector_nonnegative hcenter) hA hb (pointVector_memR center)


theorem matrixVectorAffine_memR_matVec {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i) (matrixVectorAffine I B X) := by
  simpa [affineMap] using matrixVectorAffine_memR_affineMap hA hb hx



theorem matrixVectorAffineNonneg_memR_matVec {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  simpa [affineMap] using
    matrixVectorAffineNonneg_memR_affineMap hI hX hA hb hx


theorem matrixVectorAffineResidual_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i - x i)
      (matrixVectorAffineResidual I B X) := by
  simpa [affineMap] using matrixVectorAffineResidual_memR_affineMap hA hb hx



theorem matrixVectorAffineResidualNonneg_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  simpa [affineMap] using
    matrixVectorAffineResidualNonneg_memR_affineMap hI hX hA hb hx


noncomputable def offDiagAbsRowSum {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, if j = i then 0 else |A i j|



noncomputable def IntervalOffDiagAbsRowSum {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) : ℚ :=
  ∑ j, if j = i then 0 else (I i j).absUpper


theorem IntervalOffDiagAbsRowSum_nonneg {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) :
    0 ≤ IntervalOffDiagAbsRowSum I i := by
  classical
  unfold IntervalOffDiagAbsRowSum
  exact Finset.sum_nonneg fun j _ => by
    by_cases h : j = i
    · simp [h]
    · simp [h, absUpper_nonneg]


theorem IntervalOffDiagAbsRowSum_nonneg_real {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) :
    0 ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
  exact_mod_cast IntervalOffDiagAbsRowSum_nonneg I i



theorem matVec_eq_diag_add_offDiag {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    matVec A x i =
      A i i * x i + ∑ j, if j = i then 0 else A i j * x j := by
  classical
  unfold matVec
  calc
    (∑ j, A i j * x j) =
        ∑ j, ((if j = i then A i j * x j else 0) +
          (if j = i then 0 else A i j * x j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h]
    _ = (∑ j, if j = i then A i j * x j else 0) +
        ∑ j, if j = i then 0 else A i j * x j := by
      rw [Finset.sum_add_distrib]
    _ = A i i * x i + ∑ j, if j = i then 0 else A i j * x j := by
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro hi
        simp at hi



theorem offDiag_abs_matVec_bound {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |∑ j, if j = i then 0 else A i j * x j| ≤
      offDiagAbsRowSum A i * |x i| := by
  classical
  calc
    |∑ j, if j = i then 0 else A i j * x j| ≤
        ∑ j, |if j = i then 0 else A i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (if j = i then 0 else |A i j| * |x j|) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h, abs_mul]
    _ ≤ ∑ j, (if j = i then 0 else |A i j| * |x i|) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j = i
      · simp [h]
      · simpa [h] using
          mul_le_mul_of_nonneg_left (hpivot j) (abs_nonneg (A i j))
    _ = offDiagAbsRowSum A i * |x i| := by
      simp [offDiagAbsRowSum, Finset.sum_mul]




theorem gershgorin_row_bound_of_pivot {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (lam : ℝ) (i : Fin n)
    (heig_i : matVec A x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |lam - A i i| ≤ offDiagAbsRowSum A i := by
  have hpos : 0 < |x i| := abs_pos.mpr hxi
  have hmul : (lam - A i i) * x i =
      ∑ j, if j = i then 0 else A i j * x j := by
    have hdecomp := matVec_eq_diag_add_offDiag A x i
    rw [heig_i] at hdecomp
    calc
      (lam - A i i) * x i = lam * x i - A i i * x i := by ring
      _ = ∑ j, if j = i then 0 else A i j * x j := by linarith
  have hbound :
      |(lam - A i i) * x i| ≤ offDiagAbsRowSum A i * |x i| := by
    rw [hmul]
    exact offDiag_abs_matVec_bound A x i hpivot
  have hbound' :
      |lam - A i i| * |x i| ≤ offDiagAbsRowSum A i * |x i| := by
    simpa [abs_mul] using hbound
  exact le_of_mul_le_mul_right hbound' hpos



theorem offDiagAbsRowSum_le_interval {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (i : Fin n) :
    offDiagAbsRowSum A i ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
  classical
  calc
    offDiagAbsRowSum A i = ∑ j, if j = i then 0 else |A i j| := rfl
    _ ≤ ∑ j, if j = i then 0 else ((I i j).absUpper : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j = i
      · simp [h]
      · simpa [h] using abs_le_absUpper_of_memR (hA i j)
    _ = (IntervalOffDiagAbsRowSum I i : ℝ) := by
      rw [IntervalOffDiagAbsRowSum, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h]


theorem gershgorin_interval_row_bound_of_pivot {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ) (i : Fin n)
    (heig_i : matVec A x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    |lam - A i i| ≤ (IntervalOffDiagAbsRowSum I i : ℝ) :=
  le_trans (gershgorin_row_bound_of_pivot A x lam i heig_i hxi hpivot)
    (offDiagAbsRowSum_le_interval hA i)


theorem exists_pivot_of_exists_nonzero {n : ℕ} (x : Fin n → ℝ)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, x i ≠ 0 ∧ ∀ j, |x j| ≤ |x i| := by
  classical
  rcases hnonzero with ⟨i0, hi0⟩
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun i => |x i|) ⟨i0, by simp⟩
  refine ⟨i, ?_, ?_⟩
  · by_contra hxi
    have hxi_zero : x i = 0 := by simpa using hxi
    have hle : |x i0| ≤ 0 := by
      simpa [hxi_zero] using hmax i0 (by simp)
    exact (not_le.mpr (abs_pos.mpr hi0)) hle
  · intro j
    exact hmax j (by simp)



theorem gershgorin_bound_of_eigenvector {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, |lam - A i i| ≤ offDiagAbsRowSum A i := by
  rcases exists_pivot_of_exists_nonzero x hnonzero with ⟨i, hxi, hpivot⟩
  exact ⟨i, gershgorin_row_bound_of_pivot A x lam i (heig i) hxi hpivot⟩



theorem gershgorin_interval_bound_of_eigenvector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, |lam - A i i| ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
  rcases exists_pivot_of_exists_nonzero x hnonzero with ⟨i, hxi, hpivot⟩
  exact ⟨i,
    gershgorin_interval_row_bound_of_pivot hA x lam i (heig i) hxi hpivot⟩



def IntervalGershgorinRowDisk {n : ℕ}
    (I : IntervalMatrix n n) (lam : ℝ) (i : Fin n) : Prop :=
  ∃ a : ℝ, (I i i).MemR a ∧
    |lam - a| ≤ (IntervalOffDiagAbsRowSum I i : ℝ)



noncomputable def IntervalGershgorinRowInterval {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) : RatInterval where
  lower := (I i i).lower - IntervalOffDiagAbsRowSum I i
  upper := (I i i).upper + IntervalOffDiagAbsRowSum I i
  lower_le_upper := by
    have hdiag := (I i i).lower_le_upper
    have hradius := IntervalOffDiagAbsRowSum_nonneg I i
    linarith



theorem mem_intervalGershgorinRowInterval_of_rowDisk {n : ℕ}
    {I : IntervalMatrix n n} {lam : ℝ} {i : Fin n}
    (hdisk : IntervalGershgorinRowDisk I lam i) :
    (IntervalGershgorinRowInterval I i).MemR lam := by
  rcases hdisk with ⟨a, ha, hdist⟩
  rw [abs_le] at hdist
  constructor
  · simpa [IntervalGershgorinRowInterval] using (by
      linarith [ha.1, hdist.1])
  · simpa [IntervalGershgorinRowInterval] using (by
      linarith [ha.2, hdist.2])



theorem intervalGershgorinRowDisk_of_pivot {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ) (i : Fin n)
    (heig_i : matVec A x i = lam * x i)
    (hxi : x i ≠ 0)
    (hpivot : ∀ j, |x j| ≤ |x i|) :
    IntervalGershgorinRowDisk I lam i :=
  ⟨A i i, hA i i,
    gershgorin_interval_row_bound_of_pivot hA x lam i heig_i hxi hpivot⟩



theorem exists_intervalGershgorinRowDisk_of_eigenvector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, IntervalGershgorinRowDisk I lam i := by
  rcases exists_pivot_of_exists_nonzero x hnonzero with ⟨i, hxi, hpivot⟩
  exact ⟨i,
    intervalGershgorinRowDisk_of_pivot hA x lam i (heig i) hxi hpivot⟩



theorem exists_mem_intervalGershgorinRowInterval_of_eigenvector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (x : Fin n → ℝ) (lam : ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) :
    ∃ i, (IntervalGershgorinRowInterval I i).MemR lam := by
  rcases exists_intervalGershgorinRowDisk_of_eigenvector hA x lam heig hnonzero
    with ⟨i, hdisk⟩
  exact ⟨i, mem_intervalGershgorinRowInterval_of_rowDisk hdisk⟩



def GershgorinRowExcludes {n : ℕ}
    (A : Fin n → Fin n → ℝ) (lam : ℝ) (i : Fin n) : Prop :=
  offDiagAbsRowSum A i < |lam - A i i|




def IntervalGershgorinRowExcludes {n : ℕ}
    (I : IntervalMatrix n n) (lam : ℝ) (i : Fin n) : Prop :=
  ∀ a : ℝ, (I i i).MemR a →
    (IntervalOffDiagAbsRowSum I i : ℝ) < |lam - a|




def IntervalGershgorinRowEndpointSeparated {n : ℕ}
    (I : IntervalMatrix n n) (lam : ℝ) (i : Fin n) : Prop :=
  lam + (IntervalOffDiagAbsRowSum I i : ℝ) < ((I i i).lower : ℝ) ∨
    ((I i i).upper : ℝ) + (IntervalOffDiagAbsRowSum I i : ℝ) < lam




def IntervalGershgorinRowEndpointSeparatedOnIcc {n : ℕ}
    (I : IntervalMatrix n n) (lo hi : ℝ) (i : Fin n) : Prop :=
  hi + (IntervalOffDiagAbsRowSum I i : ℝ) < ((I i i).lower : ℝ) ∨
    ((I i i).upper : ℝ) + (IntervalOffDiagAbsRowSum I i : ℝ) < lo


theorem intervalGershgorinRowExcludes_of_endpointSeparated {n : ℕ}
    {I : IntervalMatrix n n} {lam : ℝ} {i : Fin n}
    (hsep : IntervalGershgorinRowEndpointSeparated I lam i) :
    IntervalGershgorinRowExcludes I lam i := by
  intro a ha
  have hR : 0 ≤ (IntervalOffDiagAbsRowSum I i : ℝ) :=
    IntervalOffDiagAbsRowSum_nonneg_real I i
  rcases hsep with hleft | hright
  · have hlt : lam < a := by linarith [ha.1]
    have hdist : |lam - a| = a - lam := by
      rw [abs_sub_comm, abs_of_nonneg]
      linarith
    rw [hdist]
    linarith [ha.1]
  · have hlt : a < lam := by linarith [ha.2]
    have hdist : |lam - a| = lam - a := by
      rw [abs_of_nonneg]
      linarith
    rw [hdist]
    linarith [ha.2]



theorem intervalGershgorinRowEndpointSeparated_of_mem_Icc {n : ℕ}
    {I : IntervalMatrix n n} {lo hi lam : ℝ} {i : Fin n}
    (hsep : IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i)
    (hlam : lam ∈ Set.Icc lo hi) :
    IntervalGershgorinRowEndpointSeparated I lam i := by
  rcases hlam with ⟨hlo, hhi⟩
  rcases hsep with hleft | hright
  · left
    linarith
  · right
    linarith



theorem no_eigenvector_of_gershgorin_exclusion {n : ℕ}
    (A : Fin n → Fin n → ℝ) (lam : ℝ)
    (hexcl : ∀ i, GershgorinRowExcludes A lam i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False := by
  rcases gershgorin_bound_of_eigenvector A x lam heig hnonzero with ⟨i, hi⟩
  exact (not_le_of_gt (hexcl i)) hi


theorem not_exists_eigenvector_of_gershgorin_exclusion {n : ℕ}
    (A : Fin n → Fin n → ℝ) (lam : ℝ)
    (hexcl : ∀ i, GershgorinRowExcludes A lam i) :
    ¬ ∃ x : Fin n → ℝ,
      (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨x, heig, hnonzero⟩
  exact no_eigenvector_of_gershgorin_exclusion A lam hexcl x heig hnonzero



theorem no_eigenvector_of_interval_gershgorin_exclusion {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hexcl : ∀ i, IntervalGershgorinRowExcludes I lam i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False := by
  rcases gershgorin_interval_bound_of_eigenvector hA x lam heig hnonzero with
    ⟨i, hi⟩
  exact (not_le_of_gt (hexcl i (A i i) (hA i i))) hi


theorem not_exists_eigenvector_of_interval_gershgorin_exclusion {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hexcl : ∀ i, IntervalGershgorinRowExcludes I lam i) :
    ¬ ∃ x : Fin n → ℝ,
      (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨x, heig, hnonzero⟩
  exact no_eigenvector_of_interval_gershgorin_exclusion hA lam hexcl x heig
    hnonzero


theorem no_eigenvector_of_interval_gershgorin_endpoint_separation {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparated I lam i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False :=
  no_eigenvector_of_interval_gershgorin_exclusion hA lam
    (fun i => intervalGershgorinRowExcludes_of_endpointSeparated (hsep i))
    x heig hnonzero



theorem not_exists_eigenvector_of_interval_gershgorin_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparated I lam i) :
    ¬ ∃ x : Fin n → ℝ,
      (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨x, heig, hnonzero⟩
  exact no_eigenvector_of_interval_gershgorin_endpoint_separation hA lam hsep
    x heig hnonzero



theorem no_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) {lo hi lam : ℝ}
    (hlam : lam ∈ Set.Icc lo hi)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False :=
  no_eigenvector_of_interval_gershgorin_endpoint_separation hA lam
    (fun i => intervalGershgorinRowEndpointSeparated_of_mem_Icc
      (hsep i) hlam)
    x heig hnonzero



theorem not_exists_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lo hi : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i) :
    ¬ ∃ lam : ℝ, lam ∈ Set.Icc lo hi ∧
      ∃ x : Fin n → ℝ,
        (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨lam, hlam, x, heig, hnonzero⟩
  exact
    no_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
      hA hlam hsep x heig hnonzero



theorem not_exists_eigenvector_in_Icc_of_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lo hi : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i) :
    ¬ ∃ lam : ℝ, lam ∈ Set.Icc lo hi ∧
      ∃ x : Fin n → ℝ,
        (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 :=
  not_exists_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
    hA lo hi hsep


structure RowSumContraction {n : ℕ} (I : IntervalMatrix n n) where
  c : ℚ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  row_bound : ∀ i, MatrixAbsRowSum I i ≤ c



structure ColumnSumContraction {n : ℕ} (I : IntervalMatrix n n) where
  c : ℚ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  col_bound : ∀ j, MatrixAbsColSum I j ≤ c



def RowSumContraction.with_larger_constant {n : ℕ}
    {I : IntervalMatrix n n} (hI : RowSumContraction I) {c' : ℚ}
    (hc : hI.c ≤ c') (hc_lt_one : c' < 1) :
    RowSumContraction I where
  c := c'
  c_nonneg := le_trans hI.c_nonneg hc
  c_lt_one := hc_lt_one
  row_bound := fun i => le_trans (hI.row_bound i) hc



def ColumnSumContraction.with_larger_constant {n : ℕ}
    {I : IntervalMatrix n n} (hI : ColumnSumContraction I) {c' : ℚ}
    (hc : hI.c ≤ c') (hc_lt_one : c' < 1) :
    ColumnSumContraction I where
  c := c'
  c_nonneg := le_trans hI.c_nonneg hc
  c_lt_one := hc_lt_one
  col_bound := fun j => le_trans (hI.col_bound j) hc



def rowSumContraction_of_pointMatrix {n : ℕ} (A : Fin n → Fin n → ℚ)
    {c : ℚ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hrow : ∀ i, (∑ j, |A i j|) ≤ c) :
    RowSumContraction (pointMatrix A) where
  c := c
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  row_bound := by
    intro i
    simpa [MatrixAbsRowSum_pointMatrix] using hrow i



def columnSumContraction_of_pointMatrix {n : ℕ} (A : Fin n → Fin n → ℚ)
    {c : ℚ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hcol : ∀ j, (∑ i, |A i j|) ≤ c) :
    ColumnSumContraction (pointMatrix A) where
  c := c
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  col_bound := by
    intro j
    simpa [MatrixAbsColSum_pointMatrix] using hcol j



theorem RowSumContraction.apply_bound {n : ℕ} {I : IntervalMatrix n n}
    (hI : RowSumContraction I) {A : Fin n → Fin n → ℝ} (hA : MatrixMem A I)
    (x : Fin n → ℝ) (i : Fin n) :
    |matVec A x i| ≤ (hI.c : ℝ) * supNormVec x := by
  classical
  have hrow : (MatrixAbsRowSum I i : ℝ) ≤ (hI.c : ℝ) := by
    exact_mod_cast hI.row_bound i
  have hsum :
      |matVec A x i| ≤
        (∑ j, |A i j|) * supNormVec x := by
    calc
      |matVec A x i| = |∑ j, A i j * x j| := rfl
      _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |x j| := by
        simp [abs_mul]
      _ ≤ ∑ j, |A i j| * supNormVec x := by
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_coord_le_supNormVec x j) (abs_nonneg _)
      _ = (∑ j, |A i j|) * supNormVec x := by
        rw [Finset.sum_mul]
  have hmatrix : (∑ j, |A i j|) ≤ (MatrixAbsRowSum I i : ℝ) :=
    MatrixMem.row_abs_sum_le hA i
  exact le_trans hsum
    (mul_le_mul_of_nonneg_right (le_trans hmatrix hrow) (supNormVec_nonneg x))



theorem RowSumContraction.constant_lt_one {n : ℕ} {I : IntervalMatrix n n}
    (hI : RowSumContraction I) : (hI.c : ℝ) < 1 := by
  exact_mod_cast hI.c_lt_one



theorem ColumnSumContraction.apply_l1_bound {n : ℕ}
    {I : IntervalMatrix n n} (hI : ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : MatrixMem A I) (x : Fin n → ℝ) :
    supNormVec (fun i => matVec A x i) ≤ (hI.c : ℝ) * supNormVec x := by
  classical
  unfold supNormVec matVec
  calc
    (∑ i, |∑ j, A i j * x j|) ≤
        ∑ i, ∑ j, |A i j * x j| := by
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, |A i j| * |x j| := by
      simp [abs_mul]
    _ = ∑ j, ∑ i, |A i j| * |x j| := by
      exact Finset.sum_comm
    _ = ∑ j, (∑ i, |A i j|) * |x j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ ∑ j, (hI.c : ℝ) * |x j| := by
      apply Finset.sum_le_sum
      intro j _
      have hcol : (∑ i, |A i j|) ≤ (hI.c : ℝ) := by
        exact le_trans (MatrixMem.col_abs_sum_le hA j)
          (by exact_mod_cast hI.col_bound j)
      exact mul_le_mul_of_nonneg_right hcol (abs_nonneg (x j))
    _ = (hI.c : ℝ) * ∑ j, |x j| := by
      rw [Finset.mul_sum]


theorem ColumnSumContraction.constant_lt_one {n : ℕ} {I : IntervalMatrix n n}
    (hI : ColumnSumContraction I) : (hI.c : ℝ) < 1 := by
  exact_mod_cast hI.c_lt_one

end RatInterval

end Exact3D
end StatMech
