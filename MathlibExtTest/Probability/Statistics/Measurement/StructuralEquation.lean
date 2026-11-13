/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Probability.Statistics.Measurement.StructuralEquation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Tests for DAG-supported nilpotency and Gaussian covariance-fit discrepancy

Boundary tests for `MathlibExt.Probability.Statistics.Measurement.StructuralEquation`:
a 3-chain, which is nilpotent, and a 2-cycle, which is not nilpotent and has no
topological order.

Boundary tests for `gaussianDiscrepancy`: one-two, singular, two-one, and
identity cases (Bartlett, STAT 241A (2007), Lemma 2).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement.Test

open MathlibExt.Probability.Statistics.Measurement

/-- The chain `0 → 1 → 2` as a coefficient matrix. -/
def chain3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 2, 0, 0; 0, 3, 0]

/-- The 2-cycle as a coefficient matrix. -/
def cycle2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem chain3_hord : ∀ v : Fin 3, v.val < Fintype.card (Fin 3) := by
  intro v
  rw [Fintype.card_fin]
  exact v.isLt

private theorem chain3_hB : ∀ i j, chain3 i j ≠ 0 → j.val < i.val := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [chain3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- `chain3 ^ 2 ≠ 0`: the `(2, 0)` entry is `6`. -/
theorem chain3_sq_ne_zero : chain3 ^ 2 ≠ 0 := by
  intro h
  have h20 : (chain3 ^ 2) 2 0 = (0 : Matrix (Fin 3) (Fin 3) ℝ) 2 0 := by rw [h]
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, chain3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.zero_apply] at h20

/-- `chain3 ^ 3 = 0` by nilpotency with `ord i = i.val`. -/
theorem chain3_cube : chain3 ^ 3 = 0 := by
  have h := pow_card_eq_zero_of_topologicalOrder (B := chain3)
    (ord := fun i => i.val) chain3_hord chain3_hB
  rwa [Fintype.card_fin] at h

/-- `(1 - chain3)⁻¹` is the finite geometric series. -/
theorem chain3_inv : (1 - chain3)⁻¹ = !![1, 0, 0; 2, 1, 0; 6, 3, 1] := by
  have h := inv_one_sub_eq_sum_pow_of_topologicalOrder (B := chain3)
    (ord := fun i => i.val) chain3_hord chain3_hB
  rw [h, Fintype.card_fin]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, pow_zero, pow_one, pow_two, chain3, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two];
    norm_num

/-- `cycle2 ^ 2 = 1`. -/
theorem cycle2_sq : cycle2 ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, cycle2, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- No power of `cycle2` vanishes. -/
theorem cycle2_not_nilpotent : ∀ n, cycle2 ^ n ≠ 0 := by
  intro n
  have hsq := cycle2_sq
  have hne : cycle2 ≠ 0 := by
    intro hcon
    have h01 : cycle2 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by rw [hcon]
    simp [cycle2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at h01
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul, pow_mul, hsq, one_pow]
    exact one_ne_zero
  · rw [pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
    exact hne

/-- `cycle2` has no topological order. -/
theorem cycle2_no_topologicalOrder :
    ¬ ∃ ord : Fin 2 → ℕ, ∀ i j, cycle2 i j ≠ 0 → ord j < ord i := by
  rintro ⟨ord, h⟩
  have h01 : cycle2 0 1 ≠ 0 := by
    simp [cycle2, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h10 : cycle2 1 0 ≠ 0 := by
    simp [cycle2, Matrix.cons_val_zero, Matrix.cons_val_one]
  have g01 := h 0 1 h01
  have g10 := h 1 0 h10
  omega

/-- One-two discrepancy value. -/
theorem discrepancy_one_two :
    gaussianDiscrepancy (1 : Matrix (Fin 1) (Fin 1) ℝ) 2
      = Real.log 2 - 1 / 2 := by
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have h2 : (2 : Matrix (Fin 1) (Fin 1) ℝ) = !![2] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.ofNat_apply]
  have hdet1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).det = 1 := by
    rw [h1]
    exact Matrix.det_fin_one_of 1
  have hdet2 : (2 : Matrix (Fin 1) (Fin 1) ℝ).det = 2 := by
    rw [h2]
    exact Matrix.det_fin_one_of 2
  have htrace : ((1 : Matrix (Fin 1) (Fin 1) ℝ)
      * (2 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).trace = 1 / 2 := by
    rw [h1, h2]
    have hinv : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
        = !![(2 : ℝ)⁻¹] := by
      rw [Matrix.inv_subsingleton]
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hinv]
    have hmul : (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
        * !![(2 : ℝ)⁻¹] = !![(2 : ℝ)⁻¹] := by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply]
    rw [hmul, Matrix.trace_fin_one_of]
    norm_num
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by simp
  unfold gaussianDiscrepancy
  rw [hdet2, htrace, hdet1, Real.log_one, hcard]
  ring

/-- One-two discrepancy is positive. -/
theorem discrepancy_one_two_pos :
    0 < gaussianDiscrepancy (1 : Matrix (Fin 1) (Fin 1) ℝ) 2 := by
  rw [discrepancy_one_two]
  have h1 : (0 : ℝ) < 1 := by norm_num
  have h := Real.lt_log_one_add_of_pos h1
  norm_num at h
  linarith

/-- Singular `S` gives negative discrepancy. -/
theorem discrepancy_singular_neg :
    gaussianDiscrepancy (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 < 0 := by
  have h0 : (0 : Matrix (Fin 1) (Fin 1) ℝ) = !![0] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hdet0 : (0 : Matrix (Fin 1) (Fin 1) ℝ).det = 0 := by
    rw [h0]
    exact Matrix.det_fin_one_of 0
  have hdet1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).det = 1 := by
    rw [h1]
    exact Matrix.det_fin_one_of 1
  have htrace : ((0 : Matrix (Fin 1) (Fin 1) ℝ)
      * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).trace = 0 := by
    rw [Matrix.zero_mul, Matrix.trace_zero]
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by simp
  unfold gaussianDiscrepancy
  rw [hdet1, htrace, hdet0, Real.log_one, Real.log_zero, hcard]
  norm_num

/-- Two-one discrepancy is positive. -/
theorem discrepancy_two_one_pos :
    0 < gaussianDiscrepancy (2 : Matrix (Fin 1) (Fin 1) ℝ) 1 := by
  have h2 : (2 : Matrix (Fin 1) (Fin 1) ℝ) = !![2] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.ofNat_apply]
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hdet2 : (2 : Matrix (Fin 1) (Fin 1) ℝ).det = 2 := by
    rw [h2]
    exact Matrix.det_fin_one_of 2
  have hdet1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).det = 1 := by
    rw [h1]
    exact Matrix.det_fin_one_of 1
  have htrace : ((2 : Matrix (Fin 1) (Fin 1) ℝ)
      * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).trace = 2 := by
    have hinv1 : (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
        = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [h1, Matrix.inv_subsingleton]
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hinv1]
    have hmul : (2 : Matrix (Fin 1) (Fin 1) ℝ)
        * (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (2 : Matrix (Fin 1) (Fin 1) ℝ) := Matrix.mul_one _
    rw [hmul, h2, Matrix.trace_fin_one_of]
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by simp
  have hval : gaussianDiscrepancy (2 : Matrix (Fin 1) (Fin 1) ℝ) 1
      = 1 - Real.log 2 := by
    unfold gaussianDiscrepancy
    rw [hdet1, htrace, hdet2, Real.log_one, hcard]
    ring
  rw [hval]
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℝ) ≠ 1 := by norm_num
  have hlt := Real.log_lt_sub_one_of_pos h2pos h2ne
  norm_num at hlt
  linarith

/-- Two-one discrepancy is nonzero. -/
theorem discrepancy_two_one_ne_zero :
    gaussianDiscrepancy (2 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠ 0 :=
  ne_of_gt discrepancy_two_one_pos

/-- Identity discrepancy vanishes. -/
theorem discrepancy_identity_zero :
    gaussianDiscrepancy (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 = 0 := by
  apply gaussianDiscrepancy_self
  rw [Matrix.det_one]
  exact isUnit_one

/-- `diagonal ![1]` is positive definite. -/
private theorem diag_one_pd :
    (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  rw [Matrix.posDef_diagonal_iff, Fin.forall_fin_one]
  norm_num [Matrix.cons_val_zero]

/-- `diagonal ![2]` is positive definite. -/
private theorem diag_two_pd :
    (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  rw [Matrix.posDef_diagonal_iff, Fin.forall_fin_one]
  norm_num [Matrix.cons_val_zero]

/-- Nonnegativity on a concrete diagonal positive-definite pair. -/
theorem discrepancy_nonneg_diag :
    0 ≤ gaussianDiscrepancy (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ) :=
  gaussianDiscrepancy_nonneg diag_one_pd diag_two_pd

/-- Forward direction of the equality case on a concrete diagonal
positive-definite pair. -/
theorem discrepancy_eq_zero_iff_mp_diag :
    (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  have h1 : (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ)
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.diagonal]
  have h0 : gaussianDiscrepancy (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
    rw [h1]
    apply gaussianDiscrepancy_self
    rw [Matrix.det_one]
    exact isUnit_one
  have hS : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := Matrix.PosDef.one
  exact (gaussianDiscrepancy_eq_zero_iff diag_one_pd hS).mp h0

/-- Backward direction of the equality case on a concrete diagonal
positive-definite pair. -/
theorem discrepancy_eq_zero_iff_mpr_diag :
    gaussianDiscrepancy (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ) = 0 :=
  (gaussianDiscrepancy_eq_zero_iff diag_two_pd diag_two_pd).mpr rfl

end MathlibExt.Probability.Statistics.Measurement.Test

end
