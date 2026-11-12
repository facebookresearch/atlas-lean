/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.CostFunction

@[expose] public section

/-! Tests for `MathlibExt.Economics.Producer.CostFunction`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Producer.CostFunction

open _root_.Economics.Producer

/-! ## Test examples -/

theorem test_costFn_eq :
    costFn ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) ![2, 3] = 2 := by
  apply costFn_eq_of_isLeast
  have himg : (fun x => (![2, 3] : Fin 2 → ℝ) ⬝ᵥ x) '' ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ))
      = {(2 : ℝ), 3} := by
    simp only [Set.image_pair]
    have h1 : (![2, 3] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 2 := by
      unfold dotProduct
      simp [Fin.sum_univ_two]
    have h2 : (![2, 3] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 3 := by
      unfold dotProduct
      simp [Fin.sum_univ_two]
    rw [h1, h2]
  rw [himg]
  constructor
  · simp
  · intro y hy
    simp at hy
    rcases hy with rfl | rfl <;> norm_num

theorem test_costFn_smul :
    costFn ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) ((2 : ℝ) • ![2, 3]) = 4 := by
  have h := costFn_smul ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ))
    (by norm_num : (0 : ℝ) ≤ 2) ![2, 3]
  rw [test_costFn_eq] at h
  exact h.trans (show (2 : ℝ) * 2 = 4 by norm_num)

theorem test_costFn_w2 :
    costFn ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) ![4, 1] = 1 := by
  apply costFn_eq_of_isLeast
  have himg : (fun x => (![4, 1] : Fin 2 → ℝ) ⬝ᵥ x) '' ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ))
      = {(4 : ℝ), 1} := by
    simp only [Set.image_pair]
    have h1 : (![4, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 4 := by
      unfold dotProduct
      simp [Fin.sum_univ_two]
    have h2 : (![4, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 1 := by
      unfold dotProduct
      simp [Fin.sum_univ_two]
    rw [h1, h2]
  rw [himg]
  constructor
  · simp
  · intro y hy
    simp at hy
    rcases hy with rfl | rfl <;> norm_num

theorem test_costFn_mid :
    costFn ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) ![3, 2] = 2 := by
  apply costFn_eq_of_isLeast
  have himg : (fun x => (![3, 2] : Fin 2 → ℝ) ⬝ᵥ x) '' ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ))
      = {(3 : ℝ), 2} := by
    simp only [Set.image_pair]
    have h1 : (![3, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 3 := by
      unfold dotProduct
      simp [Fin.sum_univ_two]
    have h2 : (![3, 2] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 2 := by
      unfold dotProduct
      simp [Fin.sum_univ_two]
    rw [h1, h2]
  rw [himg]
  constructor
  · simp
  · intro y hy
    simp at hy
    rcases hy with rfl | rfl <;> norm_num

theorem test_costFn_concave :
    (3/2 : ℝ) ≤ costFn ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)) ![3, 2] := by
  have hne : ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)).Nonempty :=
    ⟨![1, 0], by simp⟩
  have hV : ∀ x ∈ ({![1, 0], ![0, 1]} : Set (Fin 2 → ℝ)), 0 ≤ x := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · intro i; fin_cases i <;> simp
    · intro i; fin_cases i <;> simp
  have hw1 : (![2, 3] : Fin 2 → ℝ) ∈ {w : Fin 2 → ℝ | 0 ≤ w} := by
    intro i; fin_cases i <;> simp
  have hw2 : (![4, 1] : Fin 2 → ℝ) ∈ {w : Fin 2 → ℝ | 0 ≤ w} := by
    intro i; fin_cases i <;> simp
  obtain ⟨-, hle⟩ := concaveOn_costFn_nonneg hne hV
  have h := hle hw1 hw2 (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  have hmid : (1/2 : ℝ) • (![2, 3] : Fin 2 → ℝ) + (1/2 : ℝ) • (![4, 1] : Fin 2 → ℝ)
      = (![3, 2] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> simp [Pi.add_apply, smul_eq_mul] <;> ring
  rw [test_costFn_eq, test_costFn_w2, hmid] at h
  simp only [smul_eq_mul] at h
  norm_num at h
  exact h

end MathlibExtTest.Economics.Producer.CostFunction
