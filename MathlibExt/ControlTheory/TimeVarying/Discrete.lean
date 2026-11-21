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
time-varying matrix family satisfies the split law over intermediate
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
  | k + 1, j => if j = k + 1 then 1 else A k * orderedProd A k j

/-- Trajectory of the discrete time-varying system
`x (k+1) = A k *ᵥ x k + B k *ᵥ u k` from `x 0 = x0`. -/
def tvTraj {n m : Type*} [Fintype n] [Fintype m] {R : Type*} [Ring R]
    (A : ℕ → Matrix n n R) (B : ℕ → Matrix n m R) (u : ℕ → m → R) (x0 : n → R) :
    ℕ → n → R
  | 0 => x0
  | k + 1 => A k *ᵥ tvTraj A B u x0 k + B k *ᵥ u k

theorem orderedProd_self {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) (k : ℕ) :
    orderedProd A k k = 1 := by
  induction k with
  | zero => simp [orderedProd]
  | succ k ih => simp [orderedProd]

theorem orderedProd_succ_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) {j k : ℕ} (h : j ≤ k) :
    orderedProd A (k + 1) j = A k * orderedProd A k j := by
  have hne : j ≠ k + 1 := by omega
  simp [orderedProd, hne]

theorem orderedProd_mul {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) {j k m : ℕ}
    (hjm : j ≤ m) (hmk : m ≤ k) :
    orderedProd A k j = orderedProd A k m * orderedProd A m j := by
  induction k generalizing j m with
  | zero =>
    have hm : m = 0 := by omega
    subst hm
    simp [orderedProd]
  | succ k ih =>
    by_cases h : m = k + 1
    · subst h
      rw [orderedProd_self, one_mul]
    · have hmk' : m ≤ k := by omega
      have hjk : j ≤ k := by omega
      rw [orderedProd_succ_of_le A hjk, orderedProd_succ_of_le A hmk', mul_assoc,
        ih hjm hmk']

theorem orderedProd_const {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (M : Matrix n n R) (k : ℕ) :
    orderedProd (fun _ => M) k 0 = M ^ k := by
  induction k with
  | zero => simp [orderedProd_self]
  | succ k ih =>
    have hle : 0 ≤ k := by omega
    have h := orderedProd_succ_of_le (fun _ => M) hle
    simp only [h, ih, pow_succ']

theorem tvTraj_eq_orderedProd {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    {R : Type*} [Ring R] (A : ℕ → Matrix n n R) (B : ℕ → Matrix n m R)
    (u : ℕ → m → R) (x0 : n → R) (k : ℕ) :
    tvTraj A B u x0 k = orderedProd A k 0 *ᵥ x0 +
      ∑ j ∈ Finset.range k, orderedProd A k (j + 1) *ᵥ (B j *ᵥ u j) := by
  induction k with
  | zero => simp [tvTraj, orderedProd_self]
  | succ k ih =>
    have hle0 : 0 ≤ k := by omega
    have h0 : orderedProd A (k + 1) 0 = A k * orderedProd A k 0 :=
      orderedProd_succ_of_le A hle0
    have hfirst : A k *ᵥ (orderedProd A k 0 *ᵥ x0)
        = orderedProd A (k + 1) 0 *ᵥ x0 := by
      rw [h0, Matrix.mulVec_mulVec]
    have hterm : ∀ j ∈ Finset.range k,
        A k *ᵥ (orderedProd A k (j + 1) *ᵥ (B j *ᵥ u j))
          = orderedProd A (k + 1) (j + 1) *ᵥ (B j *ᵥ u j) := by
      intro j hj
      have hlt : j < k := Finset.mem_range.mp hj
      have hjk : j + 1 ≤ k := by omega
      have h := orderedProd_succ_of_le A hjk
      rw [h, Matrix.mulVec_mulVec]
    have hsum : A k *ᵥ (∑ j ∈ Finset.range k, orderedProd A k (j + 1) *ᵥ (B j *ᵥ u j))
        = ∑ j ∈ Finset.range k, orderedProd A (k + 1) (j + 1) *ᵥ (B j *ᵥ u j) := by
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl hterm
    show A k *ᵥ tvTraj A B u x0 k + B k *ᵥ u k = _
    rw [ih, Matrix.mulVec_add, hfirst, hsum, Finset.sum_range_succ, orderedProd_self,
      Matrix.one_mulVec]
    exact add_assoc _ _ _

end ControlTheory
