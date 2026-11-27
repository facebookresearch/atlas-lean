/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.BooleanCubeFKN
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.NormNum

namespace BooleanCube.FKNTest

open scoped BigOperators

private theorem eq_of_dist_nonpos {n : ℕ} {f g : BoolCube n → ℝ} (h : boolDist f g ≤ 0) :
    f = g := by
  unfold boolDist at h
  have h₀ (x : BoolCube n) : 0 ≤ (if f x ≠ g x then (1 : ℝ) else 0) := by split <;> norm_num
  have heq := h.antisymm (Finset.expect_nonneg fun x _ => h₀ x)
  have hall := (Finset.expect_eq_zero_iff_of_nonneg (fun x _ => h₀ x)).mp heq
  funext x
  by_contra hne
  simpa [hne] using hall x (Finset.mem_univ x)

/-- At zero deficit the conclusion gives pointwise equality on the entire cube. -/
example {n : ℕ} (hn : 0 < n) (f : BoolCube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hweight : (∑ S with S.card = 1, boolFourierCoeff n f S ^ 2) = 1) :
    ∃ i : Fin n, f = (fun x => cubeVal (x i)) ∨ f = (fun x => -cubeVal (x i)) := by
  obtain ⟨C, hC⟩ := fkn_theorem
  obtain ⟨i, hi⟩ := hC n hn f hf 0 (by rw [sub_zero, hweight])
  simp only [mul_zero] at hi
  exact ⟨i, hi.imp eq_of_dist_nonpos eq_of_dist_nonpos⟩

/-- In dimension one a negated coordinate has full level-one weight and disagrees with the
positive coordinate everywhere. -/
example :
    let f := fun x : BoolCube 1 => -1 * cubeChi 1 {0} x
    (∑ S with S.card = 1, boolFourierCoeff 1 f S ^ 2) = 1 ∧
      boolDist f (cubeChi 1 {0}) = 1 := by
  dsimp only
  constructor
  · rw [Finset.sum_eq_single_of_mem {0} (by simp)]
    · rw [boolFourierCoeff_const_mul, boolFourierCoeff_cubeChi_self]
      norm_num
    · intro S _ hS
      rw [boolFourierCoeff_const_mul, boolFourierCoeff_cubeChi, ite_eq_right (Ne.symm hS)]
      norm_num
  · unfold boolDist
    have hne (x : BoolCube 1) : -1 * cubeChi 1 {0} x ≠ cubeChi 1 {0} x := by
      rcases cubeChi_eq_one_or_neg_one {0} x with h | h <;> norm_num [h]
    simp only [ite_eq_left (hne _), Fintype.expect_const]

end BooleanCube.FKNTest
