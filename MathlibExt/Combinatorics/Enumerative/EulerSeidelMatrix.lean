/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Euler–Seidel matrices

Source: Ayhan Dil and István Mező, *A Symmetric Algorithm for Hyperharmonic and Fibonacci Numbers*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Euler–Seidel matrix.** Let $M$ be a type with an addition and let $(a_n)_{n \ge 0}$ be a
sequence in $M$. The Euler–Seidel matrix of $a$ is the array $(a_n^k)_{n, k \ge 0}$, with entry
$a_n^k$ in position $(n, k)$, defined by $a_n^0 = a_n$ and
$a_n^k = a_n^{k-1} + a_{n+1}^{k-1}$ for $k \ge 1$. -/
def eulerSeidelMatrix {M : Type*} [Add M] (a : ℕ → M) : ℕ → ℕ → M
  | n, 0 => a n
  | n, k + 1 => eulerSeidelMatrix a n k + eulerSeidelMatrix a (n + 1) k

open scoped BigOperators in
/-- **Closed form of the Euler–Seidel matrix.** Let $M$ be an additive commutative monoid and let
$(a_n)_{n \ge 0}$ be a sequence in $M$. For all $n, k \ge 0$, the entry $a_n^k$ of the
Euler–Seidel matrix of $a$ equals $\sum_{i=0}^{k} \binom{k}{i} a_{n+i}$. -/
public theorem eulerSeidelMatrix_eq_sum {M : Type*} [AddCommMonoid M] (a : ℕ → M)
    (n k : ℕ) :
    eulerSeidelMatrix a n k = ∑ i ∈ Finset.range (k + 1), k.choose i • a (n + i) := by
  induction k generalizing n with
  | zero =>
    have h0 : eulerSeidelMatrix a n 0 = a n := rfl
    have h01 : (0 : ℕ) + 1 = 1 := rfl
    rw [h0, h01, Finset.sum_range_one, Nat.choose_self, one_nsmul, Nat.add_zero]
  | succ k ih =>
    have hdef : eulerSeidelMatrix a n k.succ
        = eulerSeidelMatrix a n k + eulerSeidelMatrix a (n + 1) k := rfl
    have hT : (∑ i ∈ Finset.range (k.succ + 1), (k.succ).choose i • a (n + i))
        = (∑ i ∈ Finset.range (k + 1), (k + 1).choose (i + 1) • a (n + (i + 1)))
          + a n := by
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      rw [show (k + 1).choose 0 • a (n + 0) = a n from by
        rw [Nat.choose_zero_right, one_nsmul, Nat.add_zero]]
    have hsplit :
        (∑ i ∈ Finset.range (k + 1), (k + 1).choose (i + 1) • a (n + (i + 1)))
        = (∑ i ∈ Finset.range (k + 1), k.choose i • a (n + (i + 1)))
          + (∑ i ∈ Finset.range (k + 1), k.choose (i + 1) • a (n + (i + 1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.choose_succ_succ', add_nsmul]
    have hM1 : (∑ i ∈ Finset.range (k + 1), k.choose i • a (n + (i + 1)))
        = ∑ i ∈ Finset.range (k + 1), k.choose i • a (n + 1 + i) := by
      apply Finset.sum_congr rfl
      intro i _
      have e : n + (i + 1) = n + 1 + i := by omega
      rw [e]
    have hM2 : (∑ i ∈ Finset.range (k + 1), k.choose (i + 1) • a (n + (i + 1)))
        = ∑ i ∈ Finset.range k, k.choose (i + 1) • a (n + (i + 1)) := by
      have hvan : k.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [Finset.sum_range_succ, hvan, zero_nsmul, add_zero]
    have hS1 : (∑ i ∈ Finset.range (k + 1), k.choose i • a (n + i))
        = (∑ i ∈ Finset.range k, k.choose (i + 1) • a (n + (i + 1))) + a n := by
      rw [Finset.sum_range_succ']
      rw [show k.choose 0 • a (n + 0) = a n from by
        rw [Nat.choose_zero_right, one_nsmul, Nat.add_zero]]
    rw [hdef, ih, ih, hT, hsplit, hS1, hM1, hM2]
    ac_rfl

end MetaMathlibExt
