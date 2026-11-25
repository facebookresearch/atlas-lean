/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GenLeonardo
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Cross-product identity for generalized Leonardo numbers

For an integer `k`, let `L_{k,n}` and `M_{k,n}` denote the generalized Leonardo numbers and the
dual generalized Leonardo numbers. The main result is `genLeonardo_cross`: for every natural
number `n ≥ 1`,
`L_{k,n} M_{k,n+1} - L_{k,n+1} M_{k,n-1} = (k + 1) L_{k,2n} - k L_{k,n} + k`.

The proof uses the closed forms `L_{k,n} + k = (1 + k) F_{n+1}` and
`M_{k,n} + 2k = (1 + k) (F_n + F_{n+2})`, where `F_n` is the Fibonacci number, together with
the Fibonacci addition formula.
-/

namespace MetaMathlibExt

/-- The generalized Leonardo numbers shifted by `k` are `1 + k` times the Fibonacci numbers:
`L_{k,n} + k = (1 + k) F_{n+1}`. -/
private theorem genLeonardoCross_add_eq (k : ℤ) :
    ∀ n : ℕ, genLeonardo k n + k = (1 + k) * Nat.fib (n + 1)
  | 0 => by simp [genLeonardo]
  | 1 => by simp [genLeonardo, Nat.fib_two]
  | n + 2 => by
    have h0 := genLeonardoCross_add_eq k n
    have h1 := genLeonardoCross_add_eq k (n + 1)
    have hF : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      exact_mod_cast Nat.fib_add_two
    rw [genLeonardo, hF]
    linear_combination h0 + h1

/-- The dual generalized Leonardo numbers satisfy
`M_{k,n} + 2k = (1 + k) (F_n + F_{n+2})`. -/
private theorem genLeonardoCross_companion_eq (k : ℤ) (n : ℕ) :
    genLeonardoCompanion k n + 2 * k = (1 + k) * (Nat.fib n + Nat.fib (n + 2)) := by
  cases n with
  | zero => simp [genLeonardoCompanion]; ring
  | succ n =>
    change genLeonardo k n + genLeonardo k (n + 2) + 2 * k = _
    have e : genLeonardo k n + genLeonardo k (n + 2) + 2 * k
        = (genLeonardo k n + k) + (genLeonardo k (n + 2) + k) := by ring
    rw [e, genLeonardoCross_add_eq, genLeonardoCross_add_eq]
    ring

@[expose] public section

/-- **Cross-product identity for generalized Leonardo numbers.** Let $k$ be an integer, and let
$L_{k,n}$ and $M_{k,n}$ denote the generalized Leonardo numbers and the dual generalized Leonardo
numbers. For every natural number $n \ge 1$,
$$L_{k,n} M_{k,n+1} - L_{k,n+1} M_{k,n-1} = (k+1) L_{k,2n} - k L_{k,n} + k.$$

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.3 (`fq-2024-kuhapatanakul05292024-thm-2.3`). -/
public theorem genLeonardo_cross (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    genLeonardo k n * genLeonardoCompanion k (n + 1)
        - genLeonardo k (n + 1) * genLeonardoCompanion k (n - 1)
      = (k + 1) * genLeonardo k (2 * n) - k * genLeonardo k n + k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hL (i : ℕ) : genLeonardo k i = (1 + k) * Nat.fib (i + 1) - k :=
    eq_sub_of_add_eq (genLeonardoCross_add_eq k i)
  have hM (i : ℕ) : genLeonardoCompanion k i
      = (1 + k) * (Nat.fib i + Nat.fib (i + 2)) - 2 * k :=
    eq_sub_of_add_eq (genLeonardoCross_companion_eq k i)
  have hL1 : genLeonardo k (m + 1) = (1 + k) * Nat.fib (m + 2) - k := hL (m + 1)
  have hL2 : genLeonardo k (m + 2) = (1 + k) * Nat.fib (m + 3) - k := hL (m + 2)
  have hL2m : genLeonardo k (2 * m + 2) = (1 + k) * Nat.fib (2 * m + 3) - k :=
    hL (2 * m + 2)
  have hM2 : genLeonardoCompanion k (m + 2)
      = (1 + k) * (Nat.fib (m + 2) + Nat.fib (m + 4)) - 2 * k := hM (m + 2)
  have hMm : genLeonardoCompanion k m
      = (1 + k) * (Nat.fib m + Nat.fib (m + 2)) - 2 * k := hM m
  rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega,
    show 2 * (m + 1) = 2 * m + 2 by omega, hL1, hL2, hL2m, hM2, hMm]
  have e3 : (Nat.fib (m + 3) : ℤ) = (Nat.fib (m + 1) : ℤ) + (Nat.fib (m + 2) : ℤ) := by
    have h := Nat.fib_add_two (n := m + 1)
    exact_mod_cast h
  have e4 : (Nat.fib (m + 4) : ℤ) = (Nat.fib (m + 2) : ℤ) + (Nat.fib (m + 3) : ℤ) := by
    have h := Nat.fib_add_two (n := m + 2)
    exact_mod_cast h
  have em : (Nat.fib m : ℤ) = (Nat.fib (m + 2) : ℤ) - (Nat.fib (m + 1) : ℤ) := by
    have h := Nat.fib_add_two (n := m)
    have h2 : ((Nat.fib (m + 2) : ℕ) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
      exact_mod_cast h
    linear_combination -h2
  have hFib : (Nat.fib (2 * m + 3) : ℤ)
      = (Nat.fib (m + 1) : ℤ) ^ 2 + (Nat.fib (m + 2) : ℤ) ^ 2 := by
    have h := Nat.fib_add (m + 1) (m + 1)
    have h2 : ((Nat.fib (m + 1 + (m + 1) + 1) : ℕ) : ℤ)
        = ((Nat.fib (m + 1) : ℕ) : ℤ) * (Nat.fib (m + 1) : ℤ)
          + ((Nat.fib (m + 2) : ℕ) : ℤ) * (Nat.fib (m + 2) : ℤ) := by
      exact_mod_cast h
    rw [show m + 1 + (m + 1) + 1 = 2 * m + 3 by omega] at h2
    linear_combination h2
  rw [e4, e3, em]
  linear_combination -(1 + k) ^ 2 * hFib

end

end MetaMathlibExt
