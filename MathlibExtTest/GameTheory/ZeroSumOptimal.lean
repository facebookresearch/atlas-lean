/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ZeroSumOptimal
import Mathlib.Tactic

/-! # Tests for `MathlibExt.GameTheory.ZeroSumOptimal`

In the `2 × 1` game `!![1; 3]` the game value is `3`, the second row is maximin, the single column
is minimax, their profile is a saddle point, and the first row is not maximin. -/

open MathlibExt.GameTheory.ZeroSumOptimal
open Matrix
open Convexity

namespace MathlibExtTest.GameTheory.ZeroSumOptimal

/-- Column weights in the `2 × 1` example: the single column has weight `1`. -/
theorem ex_col_weights_eq_one (q : StdSimplex ℝ (Fin 1)) : q.weights 0 = 1 := by
  have h := StdSimplex.total_of_fintype q
  rw [Fin.sum_univ_one] at h
  exact h

/-- Row weights in the `2 × 1` example sum to `1`. -/
theorem ex_row_weights_sum (p : StdSimplex ℝ (Fin 2)) :
    p.weights 0 + p.weights 1 = 1 := by
  have h := StdSimplex.total_of_fintype p
  rw [Fin.sum_univ_two] at h
  exact h

theorem ex_single_one_weights_zero :
    (StdSimplex.single (R := ℝ) (1 : Fin 2)).weights 0 = 0 := by
  rw [StdSimplex.weights_single]
  exact Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)

theorem ex_single_one_weights_one :
    (StdSimplex.single (R := ℝ) (1 : Fin 2)).weights 1 = 1 := by
  rw [StdSimplex.weights_single]
  exact Finsupp.single_eq_same

theorem ex_single_zero_weights_zero :
    (StdSimplex.single (R := ℝ) (0 : Fin 2)).weights 0 = 1 := by
  rw [StdSimplex.weights_single]
  exact Finsupp.single_eq_same

theorem ex_single_zero_weights_one :
    (StdSimplex.single (R := ℝ) (0 : Fin 2)).weights 1 = 0 := by
  rw [StdSimplex.weights_single]
  exact Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide)

theorem ex_A00 : (!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) 0 0 = 1 := by simp

theorem ex_A10 : (!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) 1 0 = 3 := by simp

/-- Payoff in the `2 × 1` example in terms of row weights. -/
theorem ex_payoff_eq (p : StdSimplex ℝ (Fin 2)) (q : StdSimplex ℝ (Fin 1)) :
    p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights) =
      p.weights 0 + 3 * p.weights 1 := by
  rw [Matrix.dot_mulVec_eq_sum_sum, Fin.sum_univ_one, Fin.sum_univ_two,
    ex_A00, ex_A10, ex_col_weights_eq_one q]
  ring

/-- The best row payoff in the example is `3`. -/
theorem ex_sup_row_payoff :
    (⨆ p : StdSimplex ℝ (Fin 2), p.weights 0 + 3 * p.weights 1) = 3 := by
  have : Nonempty (StdSimplex ℝ (Fin 2)) :=
    ⟨StdSimplex.single (R := ℝ) (0 : Fin 2)⟩
  have hle : ∀ p : StdSimplex ℝ (Fin 2), p.weights 0 + 3 * p.weights 1 ≤ 3 := by
    intro p
    have hsum := ex_row_weights_sum p
    have h1 := StdSimplex.weights_apply_le_one p (1 : Fin 2)
    linarith
  have hBdd : BddAbove (Set.range fun p : StdSimplex ℝ (Fin 2) =>
      p.weights 0 + 3 * p.weights 1) := by
    refine ⟨3, ?_⟩
    intro b hb
    obtain ⟨p, rfl⟩ := hb
    exact hle p
  apply le_antisymm
  · exact ciSup_le hle
  · have h := le_ciSup hBdd (StdSimplex.single (R := ℝ) (1 : Fin 2))
    simp only [ex_single_one_weights_zero, ex_single_one_weights_one] at h
    norm_num at h
    exact h

/-- Maximin value of the example is `3`. -/
theorem ex_maximin_value :
    (⨆ p : StdSimplex ℝ (Fin 2), ⨅ q : StdSimplex ℝ (Fin 1),
      p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) = 3 := by
  have : Nonempty (StdSimplex ℝ (Fin 1)) :=
    ⟨StdSimplex.single (R := ℝ) (0 : Fin 1)⟩
  have hinner : ∀ p : StdSimplex ℝ (Fin 2),
      (⨅ q : StdSimplex ℝ (Fin 1),
        p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) =
        p.weights 0 + 3 * p.weights 1 := by
    intro p
    simp only [ex_payoff_eq]
    exact ciInf_const
  simp only [hinner]
  exact ex_sup_row_payoff

/-- Minimax value of the example is `3`. -/
theorem ex_minimax_value :
    (⨅ q : StdSimplex ℝ (Fin 1), ⨆ p : StdSimplex ℝ (Fin 2),
      p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) = 3 := by
  have : Nonempty (StdSimplex ℝ (Fin 1)) :=
    ⟨StdSimplex.single (R := ℝ) (0 : Fin 1)⟩
  have hsup : ∀ q : StdSimplex ℝ (Fin 1),
      (⨆ p : StdSimplex ℝ (Fin 2),
        p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) = 3 := by
    intro q
    simp only [ex_payoff_eq]
    exact ex_sup_row_payoff
  simp only [hsup]
  exact ciInf_const

/-- The example game has a value. -/
theorem ex_has_value :
    (⨆ p : StdSimplex ℝ (Fin 2), ⨅ q : StdSimplex ℝ (Fin 1),
      p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) =
      ⨅ q : StdSimplex ℝ (Fin 1), ⨆ p : StdSimplex ℝ (Fin 2),
        p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights) :=
  ex_maximin_value.trans ex_minimax_value.symm

/-- Row `1` is maximin in the example. -/
theorem ex_maximin_single_one :
    IsMaximinStrategy (!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ)
      (StdSimplex.single (R := ℝ) (1 : Fin 2)) := by
  have : Nonempty (StdSimplex ℝ (Fin 1)) :=
    ⟨StdSimplex.single (R := ℝ) (0 : Fin 1)⟩
  have hLHS : (⨅ q : StdSimplex ℝ (Fin 1),
      (StdSimplex.single (R := ℝ) (1 : Fin 2)).weights ⬝ᵥ
        ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) = 3 := by
    simp only [ex_payoff_eq, ex_single_one_weights_zero, ex_single_one_weights_one,
      ciInf_const]
    norm_num
  exact hLHS.trans ex_maximin_value.symm

/-- The single column is minimax in the example. -/
theorem ex_minimax_single_zero :
    IsMinimaxStrategy (!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ)
      (StdSimplex.single (R := ℝ) (0 : Fin 1)) := by
  have hLHS : (⨆ p : StdSimplex ℝ (Fin 2),
      p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ
        (StdSimplex.single (R := ℝ) (0 : Fin 1)).weights)) = 3 := by
    simp only [ex_payoff_eq]
    exact ex_sup_row_payoff
  exact hLHS.trans ex_minimax_value.symm

/-- The optimal pair is a Nash equilibrium in the example. -/
theorem ex_nash :
    (∀ p' : StdSimplex ℝ (Fin 2),
      p'.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ
          (StdSimplex.single (R := ℝ) (0 : Fin 1)).weights) ≤
        (StdSimplex.single (R := ℝ) (1 : Fin 2)).weights ⬝ᵥ
          ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ
            (StdSimplex.single (R := ℝ) (0 : Fin 1)).weights)) ∧
      ∀ q' : StdSimplex ℝ (Fin 1),
        (StdSimplex.single (R := ℝ) (1 : Fin 2)).weights ⬝ᵥ
            ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ
              (StdSimplex.single (R := ℝ) (0 : Fin 1)).weights) ≤
          (StdSimplex.single (R := ℝ) (1 : Fin 2)).weights ⬝ᵥ
            ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q'.weights) :=
  isSaddlePoint_of_optimal_of_value_eq ex_has_value ex_maximin_single_one ex_minimax_single_zero

/-- The optimal pair is a Nash equilibrium in the example, in the canonical
`IsMixedNash` form with payoffs `A` and `-A`. -/
theorem ex_isMixedNash :
    MathlibExt.GameTheory.MixedNashExistence.IsMixedNash
      (zeroSumPayoffs (!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ))
      (zeroSumProfile (StdSimplex.single (R := ℝ) (1 : Fin 2))
        (StdSimplex.single (R := ℝ) (0 : Fin 1))) :=
  isMixedNash_of_optimal_of_value_eq ex_has_value ex_maximin_single_one ex_minimax_single_zero

/-- Row `0` is not maximin in the example: it guarantees only `1 < 3`. -/
theorem ex_not_maximin_single_zero :
    ¬ IsMaximinStrategy (!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ)
      (StdSimplex.single (R := ℝ) (0 : Fin 2)) := by
  have : Nonempty (StdSimplex ℝ (Fin 1)) :=
    ⟨StdSimplex.single (R := ℝ) (0 : Fin 1)⟩
  have hLHS : (⨅ q : StdSimplex ℝ (Fin 1),
      (StdSimplex.single (R := ℝ) (0 : Fin 2)).weights ⬝ᵥ
        ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) = 1 := by
    simp only [ex_payoff_eq, ex_single_zero_weights_zero, ex_single_zero_weights_one,
      ciInf_const]
    norm_num
  intro h
  have hcon : (⨅ q : StdSimplex ℝ (Fin 1),
      (StdSimplex.single (R := ℝ) (0 : Fin 2)).weights ⬝ᵥ
        ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) =
      (⨆ p : StdSimplex ℝ (Fin 2), ⨅ q : StdSimplex ℝ (Fin 1),
        p.weights ⬝ᵥ ((!![1; 3] : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ q.weights)) := h
  rw [hLHS, ex_maximin_value] at hcon
  norm_num at hcon

end MathlibExtTest.GameTheory.ZeroSumOptimal
