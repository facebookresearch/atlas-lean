/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HybridPrimeDivisorBoundsHybridBoundPrimeDivisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the hybrid prime divisor bound

We test the empty factorization, a zero-sized class, a finite prime class, and
an exponent whose prime factors are listed in decreasing order.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Theorem 1.
-/

namespace MathlibExtTest.NumberTheory.HybridPrimeDivisorBoundsHybridBoundPrimeDivisors

example {x : ℕ} (hx : 1 < x) :
    ∃ r : ℕ, r = (x - 1).primeFactors.card ∧
      (∀ i < r, 0 < Nat.nth Nat.Prime i) ∧
      1 + ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i ≤ x := by
  obtain ⟨k, hsum, hpos, hbound⟩ := MetaMathlibExt.hybrid_bound_prime_divisors
    0 (fun _ => 0) (fun _ => 0) (by simp) (by simp [Set.InjOn]) (by simp) hx
  refine ⟨k 0, ?_, ?_, ?_⟩
  · simpa using hsum
  · simpa using hpos 0 le_rfl
  · simpa using hbound 0 le_rfl

example : ∃ k : ℕ → ℕ, k 0 = 0 ∧ k 1 = 1 := by
  obtain ⟨k, hsum, hpos, hbound⟩ := MetaMathlibExt.hybrid_bound_prime_divisors
    1 (fun _ => 3) (fun _ => 1) (by norm_num)
    (by simp [Set.InjOn]) (by simp) (x := 2) (by decide)
  have hsum' : k 0 + k 1 = 1 := by
    simpa [Finset.sum_range_succ, Nat.Prime.primeFactors (by norm_num : Nat.Prime 7)] using hsum
  have hbound' : 1 + ∏ i ∈ Finset.range (k 0),
      Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 3 ρ 1) i ≤ 2 := by
    simpa only [Nat.zero_add, Finset.prod_range_one,
      Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1),
      Finset.prod_empty, pow_one, true_or, true_and,
      show Finset.Ioc 0 1 = {1} from by decide, Finset.mem_singleton, forall_eq] using
      hbound 0 (by decide)
  have hk : k 0 = 0 := by
    by_contra hk
    have hprod : 2 ^ k 0 ≤ ∏ i ∈ Finset.range (k 0),
        Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 3 ρ 1) i := by
      have hle : ∀ i ∈ Finset.range (k 0),
          2 ≤ Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 3 ρ 1) i := by
        intro i hi
        have hpositive : 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 3 ρ 1) i := by
          simpa [show Finset.Ioc 0 1 = {1} from by decide] using
            hpos 0 (by decide) i (Finset.mem_range.mp hi)
        exact (Nat.nth_mem_of_ne_zero hpositive.ne').1.two_le
      simpa using Finset.prod_le_prod hle
    have htwo : 1 < 2 ^ k 0 := one_lt_pow₀ (by decide) hk
    omega
  exact ⟨k, hk, by omega⟩

example : ∃ k : ℕ → ℕ, k 0 + k 1 = 1 ∧
    ∀ i < k 0, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i := by
  obtain ⟨k, hsum, hpos, _⟩ := MetaMathlibExt.hybrid_bound_prime_divisors
    1 (fun _ => 2) (fun _ => 1) (by norm_num)
    (by simp [Set.InjOn]) (by simp) (x := 3) (by decide)
  refine ⟨k, ?_, ?_⟩
  · simpa [Finset.sum_range_succ, show (8 : ℕ).primeFactors = {2} from by
      rw [show (8 : ℕ) = 2 ^ 3 from by norm_num,
        Nat.primeFactors_prime_pow (by decide) Nat.prime_two]] using hsum
  · simpa [show Finset.Ioc 0 1 = {1} from by decide] using hpos 0 (by decide)

example : ∃ k : ℕ → ℕ, k 0 + k 1 + k 2 = 2 := by
  let p : ℕ → ℕ := fun i => if i = 1 then 3 else 2
  have hp : ∀ i ∈ Finset.Icc 1 2, (p i).Prime := by
    intro i hi
    have hi' : i = 1 ∨ i = 2 := by have := Finset.mem_Icc.mp hi; omega
    rcases hi' with rfl | rfl <;> norm_num [p]
  have hinj : Set.InjOn p (Finset.Icc 1 2) := by
    intro i hi j hj hij
    have hi' : i = 1 ∨ i = 2 := by have := Finset.mem_Icc.mp hi; omega
    have hj' : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.mp hj; omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp_all [p]
  obtain ⟨k, hsum, _, _⟩ := MetaMathlibExt.hybrid_bound_prime_divisors
    2 p (fun _ => 1) hp hinj (by simp) (x := 2) (by decide)
  refine ⟨k, ?_⟩
  have hprod : (∏ i ∈ Finset.Icc 1 2, p i ^ 1) = 6 := by decide
  have hcard : (63 : ℕ).primeFactors.card = 2 := by
    rw [show (63 : ℕ) = 3 ^ 2 * 7 from by norm_num,
      Nat.primeFactors_mul (by norm_num) (by decide),
      Nat.primeFactors_prime_pow (by decide) (by norm_num),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 7)]
    decide
  rw [hprod] at hsum
  simpa [Finset.sum_range_succ, hcard] using hsum

end MathlibExtTest.NumberTheory.HybridPrimeDivisorBoundsHybridBoundPrimeDivisors
