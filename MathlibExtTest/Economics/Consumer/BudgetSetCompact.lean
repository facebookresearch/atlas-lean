/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.BudgetSetCompact

/-!
# Tests for compactness of budget sets

The budget set at prices `(1, 2)` and wealth `4` is compact, contains `(4, 0)` and buys at most `2`
units of the second good; at prices `(0, 1)` and wealth `1` it is nonempty but unbounded, so not
compact; at negative wealth it is empty.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Consumer.BudgetSetCompact

open _root_.Economics.Consumer

theorem pos12 : ∀ i : Fin 2, (0:ℝ) < (![1, 2] : Fin 2 → ℝ) i := by
  rw [Fin.forall_fin_two]
  constructor <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem compact12 : IsCompact (nonnegBudgetSet (![1, 2] : Fin 2 → ℝ) 4) :=
  isCompact_nonnegBudgetSet pos12

theorem nonneg40 : ∀ i : Fin 2, (0:ℝ) ≤ (![4, 0] : Fin 2 → ℝ) i := by
  rw [Fin.forall_fin_two]
  constructor <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem mem12 : (![4, 0] : Fin 2 → ℝ) ∈ nonnegBudgetSet (![1, 2] : Fin 2 → ℝ) 4 := by
  refine ⟨nonneg40, ?_⟩
  show (∑ i, (![1, 2] : Fin 2 → ℝ) i * ![4, 0] i) ≤ 4
  rw [Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem unbounded01 : ¬ Bornology.IsBounded (nonnegBudgetSet (![0, 1] : Fin 2 → ℝ) 1) := by
  intro h
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le h
  have hmem : ∀ i : Fin 2, (0:ℝ) ≤ (![|C| + 1, 0] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      have h := abs_nonneg C
      linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact le_rfl
  have hy0 : (0 : Fin 2 → ℝ) ≤ ![|C| + 1, 0] := hmem
  have hcost : (![0, 1] : Fin 2 → ℝ) ⬝ᵥ ![|C| + 1, 0] ≤ 1 := by
    show (∑ i, (![0, 1] : Fin 2 → ℝ) i * ![|C| + 1, 0] i) ≤ 1
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hle : ‖![|C| + 1, 0]‖ ≤ C :=
    hC (![|C| + 1, 0] : Fin 2 → ℝ) ⟨hy0, hcost⟩
  have hge : |C| + 1 ≤ ‖![|C| + 1, 0]‖ := by
    have h1 : ‖(![|C| + 1, 0] : Fin 2 → ℝ) 0‖ ≤ ‖![|C| + 1, 0]‖ :=
      norm_le_pi_norm _ 0
    rw [Matrix.cons_val_zero, Real.norm_eq_abs] at h1
    have hnn : (0:ℝ) ≤ |C| + 1 := by
      have h := abs_nonneg C
      linarith
    rwa [abs_of_nonneg hnn] at h1
  have hlt : C < |C| + 1 := by
    have h := le_abs_self C
    linarith
  linarith

theorem notcompact01 : ¬ IsCompact (nonnegBudgetSet (![0, 1] : Fin 2 → ℝ) 1) := by
  intro hc
  exact unbounded01 hc.isBounded

theorem empty_neg : nonnegBudgetSet (![1, 2] : Fin 2 → ℝ) (-1) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨hx0, hcost⟩ := hx
  have hnn : (0:ℝ) ≤ (![1, 2] : Fin 2 → ℝ) ⬝ᵥ x := by
    show (0:ℝ) ≤ ∑ i, (![1, 2] : Fin 2 → ℝ) i * x i
    exact Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (pos12 i)) (hx0 i)
  linarith

theorem bound_x1_via_subset :
    ∀ x ∈ nonnegBudgetSet (![1, 2] : Fin 2 → ℝ) 4, x 1 ≤ 2 := by
  intro x hx
  have hmem := nonnegBudgetSet_subset_Icc pos12 hx
  obtain ⟨_, hle⟩ := Set.mem_Icc.mp hmem
  have h1 : x 1 ≤ 4 / (![1, 2] : Fin 2 → ℝ) 1 := hle 1
  have hval : (![1, 2] : Fin 2 → ℝ) 1 = 2 := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hval] at h1
  norm_num at h1
  exact h1

theorem nonempty01_via_nonempty :
    (nonnegBudgetSet (![0, 1] : Fin 2 → ℝ) 1).Nonempty :=
  nonnegBudgetSet_nonempty zero_le_one

end MathlibExtTest.Economics.Consumer.BudgetSetCompact
