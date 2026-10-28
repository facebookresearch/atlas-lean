/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic

/-! Equality of real vectors from norm preservation and agreement on the original support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Matching the original support and preserving its squared norm forces equality everywhere. -/
theorem generatedFourth_real_eq_of_norm_support {I : Type*} [Fintype I]
    (x y : I → ℝ) (hn : (∑ i, y i ^ 2) = ∑ i, x i ^ 2)
    (hs : ∀ i, x i ≠ 0 → y i = x i) : y = x := by
  classical
  have hc : (∑ i, y i * x i) = ∑ i, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i = 0
    · norm_num [h]
    · rw [hs i h, pow_two]
  have hd : (∑ i, (y i - x i) ^ 2) = 0 := by
    simp_rw [show ∀ i, (y i - x i) ^ 2 = y i ^ 2 + x i ^ 2 - 2 * (y i * x i) from
      fun i => by ring]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hc, hn]
    ring
  funext i
  have hi : (y i - x i) ^ 2 ≤ ∑ j, (y j - x j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (y j - x j)) (Finset.mem_univ i)
  rw [hd] at hi
  nlinarith [sq_nonneg (y i - x i)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
