/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dispersion of the eigenvalues of a real symmetric matrix

For a real symmetric matrix `A` of size `m`, the trace of `A²` is the second power sum
of its eigenvalues, counted with multiplicity. The difference `m tr(A²) − tr(A)²` measures
their spread: it is nonnegative, and vanishes exactly on scalar matrices, including in
empty dimension. No invertibility or positivity assumption is needed.
-/

public section

open scoped BigOperators
open Unitary

namespace Matrix.IsHermitian

variable {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}

/-- The trace of the square of a real symmetric matrix is the sum of the squares of its
real eigenvalues, with multiplicity. -/
theorem trace_sq_eq_sum_sq_eigenvalues (h : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, h.eigenvalues i ^ 2 := by
  conv_lhs => rw [h.spectral_theorem, ← map_pow, diagonal_pow, conjStarAlgAut_apply,
    trace_mul_cycle, coe_star_mul_self, one_mul, trace_diagonal]
  rfl

/-- Cauchy–Schwarz for the eigenvalues of a real symmetric matrix, in trace form. -/
theorem trace_dispersion_nonneg (h : A.IsHermitian) :
    0 ≤ m * (A ^ 2).trace - A.trace ^ 2 := by
  rw [h.trace_sq_eq_sum_sq_eigenvalues, h.trace_eq_sum_eigenvalues, sub_nonneg]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1 : ℝ))
    h.eigenvalues

private lemma centered_sum (x : Fin m → ℝ) (s : ℝ) :
    ∑ i, (x i - s) ^ 2 = ∑ i, x i ^ 2 - 2 * (∑ i, x i) * s + m * s ^ 2 := by
  simp [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]

/-- A real symmetric matrix has zero trace dispersion if and only if it is scalar. -/
theorem trace_dispersion_eq_zero_iff (h : A.IsHermitian) :
    m * (A ^ 2).trace - A.trace ^ 2 = 0 ↔ ∃ c : ℝ, A = c • 1 := by
  constructor
  · intro hd
    obtain rfl | hm := Nat.eq_zero_or_pos m
    · exact ⟨0, Subsingleton.elim _ _⟩
    have hm' : (m : ℝ) ≠ 0 := by positivity
    let s := A.trace / m
    have hs : ∑ i, (h.eigenvalues i - s) ^ 2 = 0 := by
      have ht : A.trace = ∑ i, h.eigenvalues i := by simpa using h.trace_eq_sum_eigenvalues
      rw [centered_sum, ← h.trace_sq_eq_sum_sq_eigenvalues, ← ht]
      dsimp [s]
      field_simp
      linear_combination hd
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (h.eigenvalues i - s))).1 hs
    have he : (RCLike.ofReal ∘ h.eigenvalues : Fin m → ℝ) = s • (fun _ => 1) := by
      funext i
      simpa using sub_eq_zero.mp (sq_eq_zero_iff.mp (hx i (Finset.mem_univ i)))
    refine ⟨s, ?_⟩
    conv_lhs => rw [h.spectral_theorem, he, diagonal_smul, diagonal_one, map_smul, map_one]
  · rintro ⟨c, rfl⟩
    simp [sq, trace_smul, smul_eq_mul]
    ring

end Matrix.IsHermitian
