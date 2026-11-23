/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Periodic

/-! # Composite values of the shifted Fibonacci sequence

We work modulo the product of 2, 3, 5, 7, 11, 23 and 31. The Fibonacci pair returns to
its initial residues after 240 steps. Over one period the gcd of each shifted term with
this product lies between 2 and 14474, so it is a nontrivial proper divisor.
-/

namespace MetaMathlibExt

namespace ShiftedLucasComposite

private abbrev modulus : ℕ := 2 * 3 * 5 * 7 * 11 * 23 * 31

private theorem fib_periodic : Function.Periodic (fun n => Nat.fib n % modulus) 240 := by
  intro n
  change Nat.ModEq modulus (Nat.fib (n + 240)) (Nat.fib n)
  induction n using Nat.twoStepInduction with
  | zero => decide +kernel
  | one => decide +kernel
  | more n ih₀ ih₁ =>
    rw [Nat.add_right_comm n 2 240, Nat.fib_add_two, Nat.fib_add_two (n := n)]
    exact ih₀.add ih₁

private theorem gcd_bounds : ∀ r < 240,
    2 ≤ Nat.gcd (Nat.fib r + 14475) modulus ∧ Nat.gcd (Nat.fib r + 14475) modulus < 14475 := by
  decide +kernel

end ShiftedLucasComposite

open ShiftedLucasComposite

/-- **Fibonacci numbers shifted by $14475$ are never prime.** Let $F_n$ be the $n$-th
Fibonacci number, with $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. For every
natural number $n$, the number $F_n + 14475$ is not prime.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 5
(`integers-2025-A42-thm-5`). -/
public theorem fib_add_14475_not_prime (n : ℕ) : ¬ (Nat.fib n + 14475).Prime := by
  have h : Nat.ModEq modulus (Nat.fib (n % 240)) (Nat.fib n) := fib_periodic.map_mod_nat n
  have bounds := gcd_bounds (n % 240) (Nat.mod_lt _ (by decide))
  rw [(h.add_right 14475).gcd_eq] at bounds
  exact Nat.not_prime_of_dvd_of_lt (Nat.gcd_dvd_left _ _) bounds.1 (by omega)

end MetaMathlibExt
