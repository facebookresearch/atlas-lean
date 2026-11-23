/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic

namespace MetaMathlibExt

@[expose] public section

/-!
# Sulanke number arrays

This module formalizes the recursive arrays in JIS statement
`jis_a908be719d10c77849cc63c2`, Pita,
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Pita/pita5.tex>, lines 1000–1051,
SHA-256 `2c3262137bb1ab4f5170f7cd1e9f38693d8ffa606fe189765b7f3ee0444ef7ed`.
Concept `jis_term_faad96daf465b7809dfe63ad`, semantic concept
`jis_sem_3fe7bd1b4773dd5d0cab4515`.
-/

/-- **Sulanke array B.** The Sulanke array $B$ assigns a natural number $B(k, i)$ to every pair of
natural numbers $k$ and $i$. It is defined by recursion on $k$: $B(0, 0) = 1$, $B(0, i) = 0$ for
$i \ge 1$, $B(k+1, 0) = B(k, 0)$, and for all $k$ and $i$

$$B(k+1, i+1) = \bigl(B(k, i+1) + 2B(k, i)\bigr) + \bigl(B(k, i) + 2B(k, i-1)\bigr),$$

where $B(k, -1)$ is read as $0$.

This is the recurrence obtained by eliminating the Sulanke array $A$, given by
$A(k+1, i) = B(k, i) + 2B(k, i-1)$, from $B(k+1, i) = A(k+1, i) + A(k+1, i-1)$, with values at
negative indices read as $0$. -/
def sulankeB : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => sulankeB k 0
  | k + 1, n + 1 =>
    (sulankeB k (n + 1) + 2 * sulankeB k n) +
      (sulankeB k n + 2 * match n with | 0 => (0 : ℕ) | m + 1 => sulankeB k m)

/-- **Sulanke array A.** The Sulanke array $A$ assigns a natural number $A(k, i)$ to every pair of
natural numbers $k$ and $i$. It is defined from the Sulanke array $B$ by $A(0, i) = 0$ for every
$i$, $A(k+1, 0) = B(k, 0)$ for every $k$, and $A(k+1, i+1) = B(k, i+1) + 2B(k, i)$ for all $k$
and $i$. -/
def sulankeA : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, 0 => sulankeB k 0
  | k + 1, n + 1 => sulankeB k (n + 1) + 2 * sulankeB k n

theorem sulankeB_zero : sulankeB 0 0 = 1 := rfl

theorem sulankeB_zero_succ (i : ℕ) : sulankeB 0 (i + 1) = 0 := rfl

theorem sulankeA_zero (i : ℕ) : sulankeA 0 i = 0 := rfl

theorem sulankeA_succ_zero (k : ℕ) : sulankeA (k + 1) 0 = sulankeB k 0 := rfl

theorem sulankeA_succ_succ (k n : ℕ) :
    sulankeA (k + 1) (n + 1) = sulankeB k (n + 1) + 2 * sulankeB k n := rfl

theorem sulankeB_succ_zero (k : ℕ) : sulankeB (k + 1) 0 = sulankeA (k + 1) 0 := rfl

theorem sulankeB_succ_succ (k n : ℕ) :
    sulankeB (k + 1) (n + 1) = sulankeA (k + 1) (n + 1) + sulankeA (k + 1) n := by
  cases n with
  | zero => simp [sulankeA, sulankeB]
  | succ m => rfl

theorem sulankeB_eq_zero_of_two_mul_lt (k : ℕ) :
    ∀ i : ℕ, 2 * k < i → sulankeB k i = 0 := by
  induction k with
  | zero =>
    intro i h
    cases i with
    | zero => omega
    | succ n => rfl
  | succ k ih =>
    intro i h
    cases i with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        have h1 : sulankeB k (0 + 1) = 0 := ih (0 + 1) (by omega)
        have h2 : sulankeB k 0 = 0 := ih 0 (by omega)
        have e : sulankeB (k + 1) (0 + 1) =
            (sulankeB k (0 + 1) + 2 * sulankeB k 0) +
              (sulankeB k 0 + 2 * (0 : ℕ)) := rfl
        simp [e, h1, h2]
      | succ m =>
        have h1 : sulankeB k (m + 1 + 1) = 0 := ih (m + 1 + 1) (by omega)
        have h2 : sulankeB k (m + 1) = 0 := ih (m + 1) (by omega)
        have h3 : sulankeB k m = 0 := ih m (by omega)
        have e : sulankeB (k + 1) (m + 1 + 1) =
            (sulankeB k (m + 1 + 1) + 2 * sulankeB k (m + 1)) +
              (sulankeB k (m + 1) + 2 * sulankeB k m) := rfl
        simp only [e, h1, h2, h3, Nat.mul_zero, Nat.add_zero]

theorem sulankeA_eq_zero_of_two_mul_le (k : ℕ) :
    ∀ i : ℕ, 2 * k ≤ i → sulankeA k i = 0 := by
  cases k with
  | zero =>
    intro i _
    rfl
  | succ k =>
    intro i h
    cases i with
    | zero => omega
    | succ n =>
      have h1 : sulankeB k (n + 1) = 0 :=
        sulankeB_eq_zero_of_two_mul_lt k (n + 1) (by omega)
      have h2 : sulankeB k n = 0 := sulankeB_eq_zero_of_two_mul_lt k n (by omega)
      have e : sulankeA (k + 1) (n + 1) =
          sulankeB k (n + 1) + 2 * sulankeB k n := rfl
      rw [e, h1, h2]

end

end MetaMathlibExt
