/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Fib.Zeckendorf

/-!
# Numeration by odd-indexed Fibonacci numbers

Greedy division by the place values `1, 2, 5, 13, …` keeps every partial sum below the
next place value. The Fibonacci recurrence then bounds individual digits and adjacent pairs.
-/

namespace MetaMathlibExt

open Finset

private def oddFib (k : ℕ) : ℕ := Nat.fib (2 * k + 1)

private lemma oddFib_succ (k : ℕ) : oddFib (k + 1) = 2 * oddFib k + Nat.fib (2 * k) := by
  change Nat.fib (2 * k + 1 + 2) = 2 * Nat.fib (2 * k + 1) + Nat.fib (2 * k)
  rw [Nat.fib_add_two (n := 2 * k + 1), Nat.fib_add_two (n := 2 * k)]
  omega

/-- Below place `n`, greedy division gives digits whose partial sums stay below the next
place value and reach `t` after the first `n` digits. -/
private lemma exists_greedy_digits (n t : ℕ) (ht : t < oddFib n) :
    ∃ a : ℕ → ℕ, ∀ m, (∑ k ∈ range m, a k * oddFib k) < oddFib m ∧
      (n ≤ m → (∑ k ∈ range m, a k * oddFib k) = t) := by
  induction n generalizing t with
  | zero =>
    have ht0 : t = 0 := Nat.lt_one_iff.mp ht
    exact ⟨fun _ ↦ 0, fun m ↦ by simp [ht0, oddFib, Nat.fib_pos]⟩
  | succ n ih =>
    have hpos : 0 < oddFib n := Nat.fib_pos.mpr (by omega)
    obtain ⟨a, ha⟩ := ih (t % oddFib n) (Nat.mod_lt _ hpos)
    refine ⟨fun k ↦ a k + if k = n then t / oddFib n else 0, fun m ↦ ?_⟩
    simp only [add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_range]
    by_cases hnm : n < m
    · rw [ite_eq_left hnm, (ha m).2 hnm.le, Nat.mod_add_div']
      exact ⟨ht.trans_le (Nat.fib_mono (by omega)), fun _ ↦ rfl⟩
    · simp [hnm, show ¬ n + 1 ≤ m from hnm, (ha m).1]

/-- **Numeration by odd-indexed Fibonacci numbers.** Let $F_n$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$). For every positive integer $t$ there are a
natural number $n$ and natural numbers $a_0, a_1, a_2, \dots$ such that
$F_{2n+1} \le t < F_{2n+3}$, $t = \sum_{k=0}^{n} a_k F_{2k+1}$, $a_0 \le 1$, $a_k \le 2$ for
every $k \ge 1$, $a_1 = 2$ and $a_0 = 1$ do not both hold, and for no $k$ do $a_{k+1} = 2$ and
$a_k = 2$ both hold.

Here $a_k$ is the coefficient the paper calls $a_{2k+1}$; the last two conditions exclude the
digit patterns $2F_3 + F_1$ and $2F_{2k+3} + 2F_{2k+1}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 1. -/
public theorem exists_odd_fib_representation {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), Nat.fib (2 * n + 1) ≤ t ∧ t < Nat.fib (2 * n + 3) ∧
      t = ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) ∧
      a 0 ≤ 1 ∧ (∀ k, 1 ≤ k → a k ≤ 2) ∧ ¬ (a 1 = 2 ∧ a 0 = 1) ∧
      ∀ k, ¬ (a (k + 1) = 2 ∧ a k = 2) := by
  let n := (t.greatestFib - 1) / 2
  have hpos := Nat.greatestFib_pos.mpr ht
  have hlo : oddFib n ≤ t := Nat.le_greatestFib.mp (by dsimp [n]; omega)
  have hhi : t < oddFib (n + 1) := Nat.greatestFib_lt.mp (by dsimp [n]; omega)
  obtain ⟨a, ha⟩ := exists_greedy_digits (n + 1) t hhi
  refine ⟨n, a, hlo, hhi, ((ha _).2 le_rfl).symm, ?_, ?_, ?_, ?_⟩
  · have h := (ha 1).1
    exact Nat.le_of_lt_succ (by simpa [oddFib, Nat.fib_add_two] using h)
  · intro k _
    have h := (ha (k + 1)).1
    rw [sum_range_succ, oddFib_succ] at h
    have hle : Nat.fib (2 * k) ≤ oddFib k := Nat.fib_le_fib_succ
    by_contra! hlarge
    have := Nat.mul_le_mul_right (oddFib k) hlarge
    omega
  · rintro ⟨h₁, h₀⟩
    have h := (ha 2).1
    simp [sum_range_succ, h₀, h₁, oddFib, Nat.fib_add_two] at h
  · intro k
    rintro ⟨h₁, h₀⟩
    have h := (ha (k + 2)).1
    have heven : Nat.fib (2 * (k + 1)) = Nat.fib (2 * k) + oddFib k := Nat.fib_add_two
    rw [sum_range_succ, sum_range_succ, h₁, h₀, oddFib_succ (k + 1), heven] at h
    have hle : Nat.fib (2 * k) ≤ oddFib k := Nat.fib_le_fib_succ
    omega

end MetaMathlibExt
