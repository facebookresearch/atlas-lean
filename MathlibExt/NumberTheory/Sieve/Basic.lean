/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Primorial
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The sifting product of a set of primes

For a decidable predicate `P` on the natural numbers and a bound `z`, the *sifting product*
`P(z) = ∏_{p ≤ z, P p} p` is the product of the primes up to `z` satisfying `P`. It is the
modulus of a sieve that removes the multiples of these primes; for `P = ⊤` it is the
primorial `z#`.

## Main definitions

* `Nat.siftingPrimorial P z`: the product of the primes `p ≤ z` with `P p`.

## Main statements

* `Nat.squarefree_prod_of_prime`: a product of distinct primes is squarefree.
* `Nat.squarefree_siftingPrimorial`, `Nat.primeFactors_siftingPrimorial`: the sifting
  product is squarefree, with prime factors the primes `p ≤ z` satisfying `P`.
* `Nat.Prime.dvd_siftingPrimorial_iff`: a prime divides `P(z)` iff it is `≤ z` and satisfies
  `P`.
* `Nat.cast_totient_eq_mul_prod_one_sub_inv`: Euler's product `φ(n) = n ∏_{p ∣ n} (1 - 1/p)`
  in any field of characteristic zero.
* `Nat.div_totient_le_two_mul_prod_one_add_inv`: `n / φ(n) ≤ 2 ∏_{p ∣ n} (1 + 1/p)`.
-/

@[expose] public section

namespace Nat

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_of_prime {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (hs p hp).squarefree
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)

/-- The sifting product `∏_{p ≤ z, P p} p` of the primes up to `z` satisfying `P`. -/
def siftingPrimorial (P : ℕ → Prop) [DecidablePred P] (z : ℕ) : ℕ :=
  ∏ p ∈ z.primesLE.filter P, p

variable {P : ℕ → Prop} [DecidablePred P] {z : ℕ}

/-- An element of a filtered `primesLE` is prime. -/
theorem prime_of_mem_primesLE_filter {p : ℕ} (hp : p ∈ z.primesLE.filter P) : p.Prime :=
  prime_of_mem_primesLE (Finset.mem_filter.mp hp).1

/-- The sifting product is squarefree. -/
theorem squarefree_siftingPrimorial (P : ℕ → Prop) [DecidablePred P] (z : ℕ) :
    Squarefree (siftingPrimorial P z) :=
  squarefree_prod_of_prime fun _ hp => prime_of_mem_primesLE_filter hp

/-- The sifting product is nonzero. -/
theorem siftingPrimorial_ne_zero (P : ℕ → Prop) [DecidablePred P] (z : ℕ) :
    siftingPrimorial P z ≠ 0 :=
  (squarefree_siftingPrimorial P z).ne_zero

/-- The prime factors of the sifting product are the primes `p ≤ z` satisfying `P`. -/
theorem primeFactors_siftingPrimorial (P : ℕ → Prop) [DecidablePred P] (z : ℕ) :
    (siftingPrimorial P z).primeFactors = z.primesLE.filter P :=
  primeFactors_prod fun _ hp => prime_of_mem_primesLE_filter hp

/-- A prime divides `P(z)` iff it is at most `z` and satisfies `P`. -/
theorem Prime.dvd_siftingPrimorial_iff {p : ℕ} (hp : p.Prime) :
    p ∣ siftingPrimorial P z ↔ p ≤ z ∧ P p := by
  have h := (mem_primeFactors_of_ne_zero (p := p) (siftingPrimorial_ne_zero P z)).symm
  rw [primeFactors_siftingPrimorial, Finset.mem_filter, mem_primesLE] at h
  constructor
  · intro hd
    obtain ⟨⟨h1, -⟩, h2⟩ := h.mp ⟨hp, hd⟩
    exact ⟨h1, h2⟩
  · intro hd
    exact (h.mpr ⟨⟨hd.1, hp⟩, hd.2⟩).2

/-- For the trivial predicate the sifting product is the primorial. -/
theorem siftingPrimorial_true (z : ℕ) : siftingPrimorial (fun _ => True) z = primorial z := by
  rw [siftingPrimorial, primorial_eq_prod_primesLE, Finset.filter_true]

/-! ### Totient products in a field of characteristic zero -/

/-- Euler's product in any field `K` of characteristic zero:
`(φ n : K) = n ∏_{p ∣ n} (1 - p⁻¹)`. This is the image of Mathlib's
`Nat.totient_eq_mul_prod_factors` (stated over `ℚ`) under `ℚ → K`. -/
theorem cast_totient_eq_mul_prod_one_sub_inv {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (totient n : K) = n * ∏ p ∈ n.primeFactors, (1 - (p : K)⁻¹) := by
  simpa using congrArg (Rat.cast : ℚ → K) (totient_eq_mul_prod_factors n)

/-- `∏_{1 < m ≤ N} (1 - 1/m²) = (N + 1) / (2N)` for `N ≥ 1`. -/
theorem prod_Ioc_one_sub_inv_sq (N : ℕ) (hN : 1 ≤ N) :
    ∏ m ∈ Finset.Ioc 1 N, (1 - ((m : ℝ) ^ 2)⁻¹) = ((N : ℝ) + 1) / (2 * N) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.prod_Ioc_succ_top (by omega), ih]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    push_cast
    field_simp
    ring

/-- `n / φ(n) = ∏_{p ∣ n} (1 - 1/p)⁻¹ ≤ 2 ∏_{p ∣ n} (1 + 1/p)` for `n ≠ 0`. -/
theorem div_totient_le_two_mul_prod_one_add_inv {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / totient n ≤ 2 * ∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹) := by
  have hq := cast_totient_eq_mul_prod_one_sub_inv (K := ℝ) n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpos : 0 < ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    refine Finset.prod_pos fun p hp => ?_
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; gcongr
    linarith
  have hsq : (1 : ℝ) / 2 ≤ ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := by
    have hsub : n.primeFactors ⊆ Finset.Ioc 1 n := by
      intro p hp
      rw [Finset.mem_Ioc]
      exact ⟨(prime_of_mem_primeFactors hp).one_lt,
        le_of_dvd (Nat.pos_of_ne_zero hn) (dvd_of_mem_primeFactors hp)⟩
    have hle := Finset.prod_le_prod_of_subset_of_le_one₀
      (f := fun m : ℕ => 1 - ((m : ℝ) ^ 2)⁻¹) hsub
      (fun m hm => by
        rw [Finset.mem_Ioc] at hm
        have h1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm.1.le
          nlinarith
        have := inv_le_one_of_one_le₀ h1
        linarith)
      (fun m _ _ => by
        have : (0 : ℝ) ≤ ((m : ℝ) ^ 2)⁻¹ := by positivity
        linarith)
    rw [prod_Ioc_one_sub_inv_sq n (Nat.one_le_iff_ne_zero.2 hn)] at hle
    refine le_trans ?_ hle
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hprod : ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) =
      (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)) * ∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    ring
  have h1 : 1 ≤ 2 * ((∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)) *
      ∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹)) := by rw [← hprod]; linarith
  rw [hq, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hn0.le]

end Nat
