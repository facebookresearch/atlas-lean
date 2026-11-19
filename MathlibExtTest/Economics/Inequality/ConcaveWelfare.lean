/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Inequality.ConcaveWelfare
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

@[expose] public section

namespace MathlibExtTest.Economics.Inequality.ConcaveWelfare

open MathlibExt.Economics.SocialWelfare

/-- Convexity of the square at two points: `(a * x + b * y)^2 ≤ a * x^2 + b * y^2`
for `a + b = 1` with `a b ≥ 0`. Used to show the test welfare is concave. -/
theorem sq_convex_two (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
  have hb1 : b = 1 - a := by linarith
  have key : a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2
      = a * (1 - a) * (x - y) ^ 2 := by rw [hb1]; ring
  have hnn : 0 ≤ a * (1 - a) * (x - y) ^ 2 :=
    mul_nonneg (mul_nonneg ha (by linarith)) (sq_nonneg _)
  linarith

/-- Test welfare function: negative sum of squares on `Fin 2 → ℝ`. -/
noncomputable def testW : (Fin 2 → ℝ) → ℝ := fun y => -(y 0 ^ 2 + y 1 ^ 2)

/-- The test welfare is concave on the whole space. -/
theorem testW_concave : ConcaveOn ℝ Set.univ testW := by
  show Convex ℝ Set.univ ∧ _
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h0 := sq_convex_two a b (x 0) (y 0) ha hb hab
  have h1 := sq_convex_two a b (x 1) (y 1) ha hb hab
  simp only [testW, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  linarith

/-- The test welfare is symmetric: relabeling does not change welfare. -/
theorem testW_symm : IsSymmetric testW := by
  intro σ y
  simp only [testW, Function.comp_apply]
  have hfin : ∀ i : Fin 2, i = 0 ∨ i = 1 :=
    Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩
  have h0 := hfin (σ 0)
  have h1 := hfin (σ 1)
  have hinj : Function.Injective σ := σ.injective
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exfalso
    have hcon : (0 : Fin 2) = 1 := hinj (by rw [h0, h1])
    exact (by decide : (0 : Fin 2) ≠ 1) hcon
  · rw [h0, h1]
  · rw [h0, h1]; ring
  · exfalso
    have hcon : (0 : Fin 2) = 1 := hinj (by rw [h0, h1])
    exact (by decide : (0 : Fin 2) ≠ 1) hcon

/-- Equalization of `![1, 3]` gives `![2, 2]` (as functions). -/
theorem test_equalize : equalize ![1, 3] = ![2, 2] := by
  funext i
  have hfin : ∀ i : Fin 2, i = 0 ∨ i = 1 :=
    Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩
  rcases hfin i with rfl | rfl
  · simp only [equalize, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fintype.card_fin]
    norm_num
  · simp only [equalize, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fintype.card_fin]
    norm_num

/-- Welfare of the unequal distribution `![1, 3]`. -/
example : testW ![1, 3] = -10 := by
  simp only [testW, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Welfare of the equalized distribution. -/
example : testW (equalize ![1, 3]) = -8 := by
  rw [test_equalize]
  simp only [testW, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Symmetric concave welfare prefers equalization, via `le_welfare_equalize`. -/
example : testW ![1, 3] ≤ testW (equalize ![1, 3]) :=
  le_welfare_equalize testW_concave testW_symm ![1, 3] (fun _ => Set.mem_univ _)

/-- Total income of `![1, 3]` is `4`. -/
theorem test_sum : ∑ i, (![1, 3] : Fin 2 → ℝ) i = 4 := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Equalization preserves the total `4`, via `sum_equalize`. -/
example : ∑ i, equalize ![1, 3] i = 4 := by
  rw [sum_equalize]
  exact test_sum

end MathlibExtTest.Economics.Inequality.ConcaveWelfare