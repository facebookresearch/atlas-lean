/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.SteinbergPresentation
public import Mathlib.GroupTheory.IsPerfect

/-! # Perfectness of the stable Steinberg group

Expresses every Steinberg generator as a commutator to prove stable perfectness.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

namespace StableSteinberg

open scoped commutatorElement

/-- The stable Steinberg group is perfect. -/
instance instIsPerfect {R : Type u} [Ring R] : Group.IsPerfect (StableSteinberg R) where
  commutator_eq_top := by
    apply top_unique
    intro g _
    have h_gen : ∀ (i j : ℕ) (hij : i ≠ j) (a : R),
        x (R := R) i j hij a ∈ _root_.commutator (StableSteinberg R) := by
      intro i j hij a
      let k := max i j + 1
      have hi_lt : i < k := by
        have h1 : i ≤ max i j := le_max_left i j
        have h2 : max i j < max i j + 1 := Nat.lt_succ_self _
        exact Nat.lt_of_le_of_lt h1 h2
      have hj_lt : j < k := by
        have h1 : j ≤ max i j := le_max_right i j
        have h2 : max i j < max i j + 1 := Nat.lt_succ_self _
        exact Nat.lt_of_le_of_lt h1 h2
      have hik : i ≠ k := Nat.ne_of_lt hi_lt
      have hkj : k ≠ j := Nat.ne_of_gt hj_lt
      have h_eq : x (R := R) i j hij a = ⁅x (R := R) i k hik a, x (R := R) k j hkj (1 : R)⁆ := by
        have h := x_chev (R := R) i k j hik hkj hij a (1 : R)
        simp only [mul_one] at h
        exact h.symm
      rw [h_eq]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h_all : ∀ (s : SteinbergGenerator R),
        (PresentedGroup.of s : StableSteinberg R) ∈ _root_.commutator (StableSteinberg R) := by
      intro s
      cases s with
      | mk i j hij a =>
        exact h_gen i j hij a
    exact PresentedGroup.generated_by
        (steinbergRelations R) (_root_.commutator (StableSteinberg R)) h_all g

end StableSteinberg

end AlgebraicKTheory

end
