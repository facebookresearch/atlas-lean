/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Discrete time-varying ordered products

The ordered product `orderedProd A k j = A (k-1) * ... * A j` of a
time-varying matrix family (the empty product `1` when `k ≤ j`) over a semiring satisfies the split law over intermediate
times and recovers ordinary powers for a constant family. The
trajectory of `x (k+1) = A k *ᵥ x k + B k *ᵥ u k` is the ordered
product applied to the initial state plus the ordered-product
convolution of the inputs.
-/

@[expose] public section

open Matrix Finset

namespace ControlTheory

/-- Ordered product of a time-varying matrix family: `orderedProd A k j`
is `A (k-1) * ... * A j` for `j < k`, and `1` when `j ≥ k`. It is defined
by recursion on the upper index. -/
def orderedProd {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Semiring R]
    (A : ℕ → Matrix n n R) : ℕ → ℕ → Matrix n n R
  | 0, _ => 1
  | k + 1, j => if k + 1 ≤ j then 1 else A k * orderedProd A k j

/-- Trajectory of the discrete time-varying system
`x (k+1) = A k *ᵥ x k + B k *ᵥ u k` from `x 0 = x0`. -/
def tvTraj {n m : Type*} [Fintype n] [Fintype m] {R : Type*} [Semiring R]
    (A : ℕ → Matrix n n R) (B : ℕ → Matrix n m R) (u : ℕ → m → R) (x0 : n → R) :
    ℕ → n → R
  | 0 => x0
  | k + 1 => A k *ᵥ tvTraj A B u x0 k + B k *ᵥ u k

theorem orderedProd_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Semiring R] (A : ℕ → Matrix n n R) {j k : ℕ} (h : k ≤ j) :
    orderedProd A k j = 1 := by
  induction k generalizing j with
  | zero => simp [orderedProd]
  | succ k ih =>
    simp only [orderedProd]
    simp [h]

theorem orderedProd_self {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Semiring R] (A : ℕ → Matrix n n R) (k : ℕ) :
    orderedProd A k k = 1 := by
  exact orderedProd_of_le A le_rfl

theorem orderedProd_succ_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Semiring R] (A : ℕ → Matrix n n R) {j k : ℕ} (h : j ≤ k) :
    orderedProd A (k + 1) j = A k * orderedProd A k j := by
  have h' : ¬ (k + 1 ≤ j) := by omega
  simp only [orderedProd]
  simp [h']

theorem orderedProd_mul {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Semiring R] (A : ℕ → Matrix n n R) {j k m : ℕ}
    (hjm : j ≤ m) (hmk : m ≤ k) :
    orderedProd A k j = orderedProd A k m * orderedProd A m j := by
  induction k generalizing m j with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    simp [orderedProd]
  | succ k ih =>
    by_cases h : m = k + 1
    · subst h
      rw [orderedProd_self]
      simp
    · have hmk' : m ≤ k := by omega
      have hjk : j ≤ k := le_trans hjm hmk'
      rw [orderedProd_succ_of_le A hjk, orderedProd_succ_of_le A hmk', mul_assoc,
        ih hjm hmk']

theorem orderedProd_const {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Semiring R] (M : Matrix n n R) (k : ℕ) :
    orderedProd (fun _ => M) k 0 = M ^ k := by
  induction k with
  | zero => rw [orderedProd_self, pow_zero]
  | succ k ih =>
    rw [orderedProd_succ_of_le _ (Nat.zero_le k), ih, pow_succ']

theorem tvTraj_eq_orderedProd {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    {R : Type*} [Semiring R] (A : ℕ → Matrix n n R) (B : ℕ → Matrix n m R)
    (u : ℕ → m → R) (x0 : n → R) (k : ℕ) :
    tvTraj A B u x0 k = orderedProd A k 0 *ᵥ x0 +
      ∑ j ∈ Finset.range k, orderedProd A k (j + 1) *ᵥ (B j *ᵥ u j) := by
  induction k with
  | zero =>
    simp [tvTraj, orderedProd_self, Matrix.one_mulVec]
  | succ k ih =>
    simp only [tvTraj]
    rw [ih]
    rw [orderedProd_succ_of_le A (Nat.zero_le k)]
    rw [← Matrix.mulVec_mulVec]
    rw [Finset.sum_range_succ]
    rw [orderedProd_self]
    simp only [Matrix.one_mulVec]
    have hsum : (∑ j ∈ Finset.range k, orderedProd A (k + 1) (j + 1) *ᵥ (B j *ᵥ u j))
        = A k *ᵥ (∑ j ∈ Finset.range k, orderedProd A k (j + 1) *ᵥ (B j *ᵥ u j)) := by
      rw [Matrix.mulVec_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j + 1 ≤ k := by
        simp [Finset.mem_range] at hj
        omega
      rw [orderedProd_succ_of_le A hjk, ← Matrix.mulVec_mulVec]
    rw [hsum]
    rw [Matrix.mulVec_add]
    rw [add_assoc]

end ControlTheory
