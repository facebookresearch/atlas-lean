/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialSpectrum

/-! The matrix and on-axis short rows of the actual axis transposition polynomial. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The quadratic matrix contraction against the physical axis vector. -/
def axisMatrixContraction {I : Type*} [Fintype I]
    (v : I → ℝ) (M : Matrix I I ℝ) : ℝ := ∑ i, ∑ j, v i * M i j * v j

/-- The actual matrix row of axial multiplication, written with its single short coefficient. -/
def axisMatrixRow {I : Type*} [Fintype I] (v : I → ℝ) (s : ℝ)
    (M : Matrix I I ℝ) (x : ℝ) : Matrix I I ℝ := fun i j =>
  4 * (v i * (∑ k, v k * M k j) + (∑ k, M i k * v k) * v j) -
    8 * s * x * v i * v j

/-- The actual on-axis short row of axial multiplication. -/
def axisMatrixShortRow {I : Type*} [Fintype I] (v : I → ℝ) (s : ℝ)
    (M : Matrix I I ℝ) (x : ℝ) : ℝ := 32 * x - 8 * s * axisMatrixContraction v M

private theorem axisMatrixContraction_columns {I : Type*} [Fintype I]
    (v : I → ℝ) (M : Matrix I I ℝ) :
    (∑ j, (∑ k, v k * M k j) * v j) = axisMatrixContraction v M := by
  simp only [Finset.sum_mul, axisMatrixContraction]
  rw [Finset.sum_comm]

private theorem axis_sum_three {I : Type*} [Fintype I]
    (a b c : ℝ) (f g : I → ℝ) :
    (∑ i, (a * f i + b * g i - c * g i)) =
      a * (∑ i, f i) + b * (∑ i, g i) - c * (∑ i, g i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem axisMatrixRow_right {I : Type*} [Fintype I]
    (v : I → ℝ) (s : ℝ) (M : Matrix I I ℝ) (x : ℝ)
    (hv : ∑ i, v i * v i = 4) (i : I) :
    (∑ j, axisMatrixRow v s M x i j * v j) =
      16 * (∑ j, M i j * v j) + (4 * axisMatrixContraction v M - 32 * s * x) * v i := by
  calc
    _ = ∑ j, ((4 * v i) * ((∑ k, v k * M k j) * v j) +
        (4 * ∑ k, M i k * v k) * (v j * v j) -
        (8 * s * x * v i) * (v j * v j)) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [axisMatrixRow]
      ring
    _ = (4 * v i) * (∑ j, (∑ k, v k * M k j) * v j) +
        (4 * ∑ k, M i k * v k) * (∑ j, v j * v j) -
        (8 * s * x * v i) * (∑ j, v j * v j) := axis_sum_three _ _ _ _ _
    _ = _ := by rw [axisMatrixContraction_columns, hv]; ring

private theorem axisMatrixRow_left {I : Type*} [Fintype I]
    (v : I → ℝ) (s : ℝ) (M : Matrix I I ℝ) (x : ℝ)
    (hv : ∑ i, v i * v i = 4) (j : I) :
    (∑ i, v i * axisMatrixRow v s M x i j) =
      16 * (∑ i, v i * M i j) + (4 * axisMatrixContraction v M - 32 * s * x) * v j := by
  have hr := axisMatrixRow_right v s M.transpose x hv j
  have hb : axisMatrixContraction v M.transpose = axisMatrixContraction v M := by
    dsimp only [axisMatrixContraction, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hh : (∑ i, axisMatrixRow v s M.transpose x j i * v i) =
      ∑ i, v i * axisMatrixRow v s M x i j := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [axisMatrixRow, Matrix.transpose_apply]
    simp only [mul_comm (v _) (M _ _)]
    ring
  rw [hh, hb] at hr
  simpa only [Matrix.transpose_apply, mul_comm (M _ _) (v _)] using hr

private theorem axisMatrixRow_contraction {I : Type*} [Fintype I]
    (v : I → ℝ) (s : ℝ) (M : Matrix I I ℝ) (x : ℝ)
    (hv : ∑ i, v i * v i = 4) :
    axisMatrixContraction v (axisMatrixRow v s M x) =
      32 * axisMatrixContraction v M - 128 * s * x := by
  have hb : axisMatrixContraction v (axisMatrixRow v s M x) =
      ∑ i, v i * (∑ j, axisMatrixRow v s M x i j * v j) := by
    simp only [axisMatrixContraction, Finset.mul_sum, mul_assoc]
  rw [hb]
  simp_rw [axisMatrixRow_right v s M x hv]
  have hm : (∑ i, v i * (∑ j, M i j * v j)) = axisMatrixContraction v M := by
    simp only [axisMatrixContraction, Finset.mul_sum, mul_assoc]
  calc
    _ = ∑ i, (16 * (v i * (∑ j, M i j * v j)) +
        (4 * axisMatrixContraction v M - 32 * s * x) * (v i * v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 16 * axisMatrixContraction v M +
        (4 * axisMatrixContraction v M - 32 * s * x) * (∑ i, v i * v i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
    _ = _ := by rw [hv]; ring

/-- The denominator-cleared transposition polynomial is the identity on the
entire matrix row, after its genuine rank-one axis term is subtracted. -/
theorem axisMatrix_transposition_polynomial {I : Type*} [Fintype I]
    (v : I → ℝ) (s : ℝ) (M : Matrix I I ℝ) (x : ℝ)
    (hv : ∑ i, v i * v i = 4) (hs : s * s = 1) (i j : I) :
    14 * M i j - 24 * (2 * axisMatrixContraction v M - 8 * s * x) *
        (2 * v i * v j) - 16 * axisMatrixRow v s M x i j +
      axisMatrixRow v s (axisMatrixRow v s M x) (axisMatrixShortRow v s M x) i j =
        14 * M i j := by
  change 14 * M i j - 24 * (2 * axisMatrixContraction v M - 8 * s * x) *
    (2 * v i * v j) -
    16 * (4 * (v i * (∑ k, v k * M k j) + (∑ k, M i k * v k) * v j) -
      8 * s * x * v i * v j) +
    (4 * (v i * (∑ k, v k * axisMatrixRow v s M x k j) +
      (∑ k, axisMatrixRow v s M x i k * v k) * v j) -
      8 * s * axisMatrixShortRow v s M x * v i * v j) = 14 * M i j
  rw [axisMatrixRow_left v s M x hv, axisMatrixRow_right v s M x hv]
  dsimp only [axisMatrixShortRow]
  linear_combination 64 * axisMatrixContraction v M * v i * v j * hs

/-- The same actual polynomial is the identity on the on-axis short coefficient. -/
theorem axisMatrixShort_transposition_polynomial {I : Type*} [Fintype I]
    (v : I → ℝ) (s : ℝ) (M : Matrix I I ℝ) (x : ℝ)
    (hv : ∑ i, v i * v i = 4) (hs : s * s = 1) :
    14 * x - 24 * (2 * axisMatrixContraction v M - 8 * s * x) * (-8 * s) -
      16 * axisMatrixShortRow v s M x +
      axisMatrixShortRow v s (axisMatrixRow v s M x) (axisMatrixShortRow v s M x) =
        14 * x := by
  dsimp only [axisMatrixShortRow]
  rw [axisMatrixRow_contraction v s M x hv]
  linear_combination -512 * x * hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
