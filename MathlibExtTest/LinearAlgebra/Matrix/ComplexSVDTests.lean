/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.ComplexSVD
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.ComplexSVDTests

open MathlibExt.LinearAlgebra.Matrix.ComplexSVDWanted

/-- The full SVD has nonincreasing singular values that vanish beyond the
codomain dimension. -/
example (A : Matrix (Fin 2) (Fin 3) ℂ) :
    ∃ (U : Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix.unitaryGroup (Fin 3) ℂ)
        (σ : Fin 3 → ℝ),
      A = (U : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0) *
        star (V : Matrix (Fin 3) (Fin 3) ℂ) ∧
      (∀ j, σ j ≤ σ 0) ∧ σ 2 = 0 := by
  obtain ⟨U, V, σ, -, hσ, hzero, hA⟩ :=
    Matrix.exists_unitaryGroup_rectangularDiagonal_antitone 2 3 A
  refine ⟨U, V, σ, hA, ?_, hzero 2 (by decide)⟩
  intro j
  exact hσ (Fin.zero_le j)

/-- A right unitary change of basis kills every column beyond the codomain
dimension. -/
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) (hj : m ≤ j.val) :
    ∃ V : Matrix.unitaryGroup (Fin n) ℂ,
      ∀ i, (A * (V : Matrix (Fin n) (Fin n) ℂ)) i j = 0 := by
  obtain ⟨U, V, σ, -, -, hzero, hAV⟩ :=
    Matrix.exists_unitaryGroup_mul_eq_rectangularDiagonal m n A
  refine ⟨V, fun i => ?_⟩
  rw [hAV, Matrix.mul_apply]
  simp [hzero j hj]

/-- The full factorization makes the second rotated column of a `1 × 2` matrix
vanish. -/
example (A : Matrix (Fin 1) (Fin 2) ℂ) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ, V ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (A * V) 0 1 = 0 := by
  obtain ⟨U, V, σ, -, -, -, hV, hA⟩ := complex_singular_value_decomposition 1 2 A
  refine ⟨V, hV, ?_⟩
  have hVtV : star (V : Matrix (Fin 2) (Fin 2) ℂ) * V = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hV
  calc
    (A * V) 0 1 =
        ((U * Matrix.of (fun (i : Fin 1) (j : Fin 2) =>
          if i.val = j.val then (σ j : ℂ) else 0) * star V) * V) 0 1 := by rw [hA]
    _ = (U * Matrix.of (fun (i : Fin 1) (j : Fin 2) =>
          if i.val = j.val then (σ j : ℂ) else 0) *
          (star V * V)) 0 1 := by rw [Matrix.mul_assoc]
    _ = (U * Matrix.of (fun (i : Fin 1) (j : Fin 2) =>
          if i.val = j.val then (σ j : ℂ) else 0)) 0 1 := by
      rw [hVtV, Matrix.mul_one]
    _ = 0 := by simp [Matrix.mul_apply]

/-- The zero matrix has all singular values zero. -/
example :
    ∃ (U : Matrix (Fin 2) (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) (σ : Fin 2 → ℝ),
      (∀ j, σ j = 0) ∧
      (0 : Matrix (Fin 2) (Fin 2) ℂ) = U * Matrix.of (fun i j =>
        if i.val = j.val then (σ j : ℂ) else 0) * star V := by
  obtain ⟨U, V, σ, -, hzero, hUmem, hVmem, hA⟩ :=
    complex_singular_value_decomposition 2 2 (0 : Matrix (Fin 2) (Fin 2) ℂ)
  refine ⟨U, V, σ, fun j => ?_, hA⟩
  have hsum := Matrix.sum_sq_singularValues_eq_sum_sq_norm_of_svd
    (0 : Matrix (Fin 2) (Fin 2) ℂ) hUmem hVmem hzero hA
  have hsum0 : ∑ j, σ j ^ 2 = 0 := by
    rw [hsum]
    simp
  have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ σ j ^ 2 := fun j _ => sq_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 j (Finset.mem_univ j)
  exact (sq_eq_zero_iff).mp h0

/-- The squared singular values of `diag (1, 2)` sum to `1 + 4 = 5`. -/
example :
    ∃ (σ : Fin 2 → ℝ), (∀ j, 0 ≤ σ j) ∧ Antitone σ ∧ ∑ j, σ j ^ 2 = 5 := by
  obtain ⟨U, V, σ, hσ, hanti, hzero, hA⟩ :=
    Matrix.exists_unitaryGroup_rectangularDiagonal_antitone 2 2 !![(1 : ℂ), 0; 0, 2]
  refine ⟨σ, hσ, hanti, ?_⟩
  have hsum := Matrix.sum_sq_singularValues_eq_sum_sq_norm_of_svd
    !![(1 : ℂ), 0; 0, 2] U.2 V.2 hzero hA
  rw [hsum]
  norm_num [Fin.sum_univ_two]

end MathlibExt.LinearAlgebra.Matrix.ComplexSVDTests
