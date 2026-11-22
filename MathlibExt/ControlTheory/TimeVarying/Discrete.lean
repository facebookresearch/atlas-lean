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
time-varying matrix family (the empty product `1` when `k ≤ j`) satisfies the split law over intermediate
times and recovers ordinary powers for a constant family. The
trajectory of `x (k+1) = A k *ᵥ x k + B k *ᵥ u k` is the ordered
product applied to the initial state plus the ordered-product
convolution of the inputs.
-/

@[expose] public section

open Matrix Finset

namespace ControlTheory

/-- Ordered product of a time-varying matrix family: `orderedProd A k j`
is `A (k-1) * ... * A j` for `j ≤ k`, and `1` when `j = k`. It is defined
by recursion on the upper index. -/
def orderedProd {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Ring R]
    (A : ℕ → Matrix n n R) : ℕ → ℕ → Matrix n n R
  | 0, _ => 1
  | k + 1, j => if k + 1 ≤ j then 1 else A k * orderedProd A k j

/-- Trajectory of the discrete time-varying system
`x (k+1) = A k *ᵥ x k + B k *ᵥ u k` from `x 0 = x0`. -/
def tvTraj {n m : Type*} [Fintype n] [Fintype m] {R : Type*} [Ring R]
    (A : ℕ → Matrix n n R) (B : ℕ → Matrix n m R) (u : ℕ → m → R) (x0 : n → R) :
    ℕ → n → R
  | 0 => x0
  | k + 1 => A k *ᵥ tvTraj A B u x0 k + B k *ᵥ u k

theorem orderedProd_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) {j k : ℕ} (h : k ≤ j) :
    orderedProd A k j = 1 := by
  cases k with
  | zero => rfl
  | succ k => simp only [orderedProd, ite_eq_left h]

theorem orderedProd_self {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) (k : ℕ) :
    orderedProd A k k = 1 :=
  orderedProd_of_le A le_rfl

theorem orderedProd_succ_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) {j k : ℕ} (h : j ≤ k) :
    orderedProd A (k + 1) j = A k * orderedProd A k j := by
  have h' : ¬ k + 1 ≤ j := by omega
  simp only [orderedProd, ite_eq_right h']

private theorem orderedProd_mul_aux {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) (k : ℕ) :
    ∀ {j m : ℕ}, j ≤ m → m ≤ k →
      orderedProd A k j = orderedProd A k m * orderedProd A m j := by
  induction k with
  | zero =>
    intro j m hjm hmk
    have hm : m = 0 := by omega
    have hj : j = 0 := by omega
    subst hm
    subst hj
    simp [orderedProd]
  | succ k ih =>
    intro j m hjm hmk
    by_cases h : m = k + 1
    · subst h
      rw [orderedProd_self, one_mul]
    · have hmk' : m ≤ k := by omega
      have h1 : orderedProd A (k + 1) j = A k * orderedProd A k j :=
        orderedProd_succ_of_le A (le_trans hjm hmk')
      have h2 : orderedProd A (k + 1) m = A k * orderedProd A k m :=
        orderedProd_succ_of_le A hmk'
      rw [h1, h2, mul_assoc, ih hjm hmk']

theorem orderedProd_mul {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) {j k m : ℕ}
    (hjm : j ≤ m) (hmk : m ≤ k) :
    orderedProd A k j = orderedProd A k m * orderedProd A m j :=
  orderedProd_mul_aux A k hjm hmk

theorem orderedProd_const {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (M : Matrix n n R) (k : ℕ) :
    orderedProd (fun _ => M) k 0 = M ^ k := by
  induction k with
  | zero => simp [orderedProd]
  | succ k ih =>
    have h : orderedProd (fun _ => M) (k + 1) 0
        = (fun _ => M) k * orderedProd (fun _ => M) k 0 :=
      orderedProd_succ_of_le _ (Nat.zero_le k)
    rw [h, ih, pow_succ']

theorem tvTraj_eq_orderedProd {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) (B : ℕ → Matrix n m R)
    (u : ℕ → m → R) (x0 : n → R) (k : ℕ) :
    tvTraj A B u x0 k = orderedProd A k 0 *ᵥ x0 +
      ∑ j ∈ Finset.range k, orderedProd A k (j + 1) *ᵥ (B j *ᵥ u j) := by
  induction k with
  | zero => simp [tvTraj, orderedProd]
  | succ k ih =>
    have hP0 : orderedProd A (k + 1) 0 = A k * orderedProd A k 0 :=
      orderedProd_succ_of_le A (Nat.zero_le k)
    have hP : ∀ j ∈ Finset.range k,
        orderedProd A (k + 1) (j + 1) = A k * orderedProd A k (j + 1) := by
      intro j hj
      apply orderedProd_succ_of_le
      have hj' : j < k := Finset.mem_range.mp hj
      omega
    have hsum : (∑ j ∈ Finset.range k, orderedProd A (k + 1) (j + 1) *ᵥ (B j *ᵥ u j))
        = ∑ j ∈ Finset.range k, (A k * orderedProd A k (j + 1)) *ᵥ (B j *ᵥ u j) :=
      Finset.sum_congr rfl (fun j hj => by rw [hP j hj])
    simp only [tvTraj, Finset.sum_range_succ, hP0, hsum, orderedProd_self,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sum, ← add_assoc,
      ← Matrix.mulVec_add, ← ih]

end ControlTheory
