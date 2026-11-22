/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Real.Basic

/-!
# An elementary lower bound for Euler's totient

For every positive `r`, `r ≤ (1 + log₂ r) * φ(r)`. Write
`r / φ(r) = ∏ p / (p - 1)` over the distinct prime factors of `r`.
Ordering those primes increasingly, the `i`-th of them is at least
`i + 1`, so the product telescopes to at most one plus the number `k`
of distinct prime factors; and `2 ^ k ≤ r`, so `k ≤ log₂ r`.
This is the elementary totient estimate behind the `O(log N)` repetition budget in Shor's
algorithm.
-/

@[expose] public section

/-- A finite set of naturals, each at least `2`, satisfies
`∏ s ≤ (1 + |s|) * ∏ (p - 1)`: peel off the largest element, which
exceeds the number of remaining elements. -/
private theorem prod_le_one_add_card_mul_prod_pred :
    ∀ (s : Finset ℕ), (∀ p ∈ s, 2 ≤ p) →
      ∏ p ∈ s, p ≤ (1 + s.card) * ∏ p ∈ s, (p - 1) := by
  intro s
  induction s using Finset.induction_on_max with
  | empty =>
    intro
    simp
  | insert a s hlt ih =>
    intro hs
    rw [Finset.forall_mem_insert] at hs
    obtain ⟨ha2, hs2⟩ := hs
    have hanmem : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ih' := ih hs2
    have hsub : insert a s ⊆ Finset.Icc 2 a := by
      intro x hx
      rw [Finset.mem_Icc]
      rcases Finset.mem_insert.mp hx with hxa | hxs
      · rw [hxa]
        exact ⟨ha2, le_refl a⟩
      · exact ⟨hs2 x hxs, le_of_lt (hlt x hxs)⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc, Finset.card_insert_of_notMem hanmem] at hcard
    have hkey : (1 + s.card) * a ≤ (1 + s.card + 1) * (a - 1) := by
      have h1 : (1 : ℕ) ≤ a := by omega
      have h2 : (1 + s.card) ≤ a - 1 := by omega
      have h3 : a = (a - 1) + 1 := (Nat.sub_add_cancel h1).symm
      calc (1 + s.card) * a
          = (1 + s.card) * (a - 1) + (1 + s.card) := by
            conv_lhs => rw [h3, mul_add, mul_one]
        _ ≤ (1 + s.card) * (a - 1) + (a - 1) := Nat.add_le_add_left h2 _
        _ = (1 + s.card + 1) * (a - 1) := by
            conv_rhs => rw [add_mul, one_mul]
    calc ∏ p ∈ insert a s, p
        = a * ∏ p ∈ s, p := Finset.prod_insert hanmem
      _ ≤ a * ((1 + s.card) * ∏ p ∈ s, (p - 1)) := Nat.mul_le_mul_left a ih'
      _ = ((1 + s.card) * a) * ∏ p ∈ s, (p - 1) := by ring
      _ ≤ ((1 + s.card + 1) * (a - 1)) * ∏ p ∈ s, (p - 1) :=
          Nat.mul_le_mul_right _ hkey
      _ = (1 + (s.card + 1)) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by ring
      _ = (1 + (insert a s).card) * ∏ p ∈ insert a s, (p - 1) := by
          rw [Finset.card_insert_of_notMem hanmem, Finset.prod_insert hanmem]

/-- A positive natural has at most `log₂ r` distinct prime factors,
since `2 ^ ω ≤ ∏ p ≤ r`. -/
private theorem card_primeFactors_le_log (r : ℕ) (hr : 0 < r) :
    r.primeFactors.card ≤ Nat.log 2 r := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  calc 2 ^ r.primeFactors.card
      = ∏ _p ∈ r.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ r.primeFactors, p :=
        Finset.prod_le_prod
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ r := Nat.le_of_dvd hr (Nat.prod_primeFactors_dvd r)

/-- For positive `r`, `φ(r) / r ≥ 1 / (1 + log₂ r)`, stated without
division. -/
theorem Nat.totient_mul_one_add_log_ge (r : ℕ) (hr : 0 < r) :
    (r : ℝ) ≤ (1 + Nat.log 2 r) * Nat.totient r := by
  have hNat : r ≤ (1 + Nat.log 2 r) * r.totient := by
    have hEq := Nat.totient_mul_prod_primeFactors r
    have hProd := prod_le_one_add_card_mul_prod_pred r.primeFactors
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have hCard := card_primeFactors_le_log r hr
    have hMpos : 0 < ∏ p ∈ r.primeFactors, (p - 1) :=
      Finset.prod_pos
        (fun p hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)
    have hPKM : ∏ p ∈ r.primeFactors, p
        ≤ (1 + Nat.log 2 r) * ∏ p ∈ r.primeFactors, (p - 1) := by
      calc ∏ p ∈ r.primeFactors, p
          ≤ (1 + r.primeFactors.card) * ∏ p ∈ r.primeFactors, (p - 1) := hProd
        _ ≤ (1 + Nat.log 2 r) * ∏ p ∈ r.primeFactors, (p - 1) :=
            Nat.mul_le_mul_right _ (by omega)
    have hMul : r * ∏ p ∈ r.primeFactors, (p - 1)
        ≤ ((1 + Nat.log 2 r) * r.totient) * ∏ p ∈ r.primeFactors, (p - 1) := by
      calc r * ∏ p ∈ r.primeFactors, (p - 1)
          = r.totient * ∏ p ∈ r.primeFactors, p := hEq.symm
        _ ≤ r.totient * ((1 + Nat.log 2 r) * ∏ p ∈ r.primeFactors, (p - 1)) :=
            Nat.mul_le_mul_left _ hPKM
        _ = ((1 + Nat.log 2 r) * r.totient) * ∏ p ∈ r.primeFactors, (p - 1) := by
            ring
    exact Nat.le_of_mul_le_mul_right hMul hMpos
  exact_mod_cast hNat
