/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Dedekind psi function

This module defines the Dedekind psi function `dedekindPsi` by the prime-power product
`ψ(n) = ∏_{p ^ k ∥ n} p ^ (k - 1) * (p + 1)` for `n > 0`, with `ψ(0) = 0`. It proves
the prime-power formula, multiplicativity, and the rational product formula
`ψ(n) = n * ∏_{p ∣ n} (1 + 1 / p)`.
-/

@[expose] public section

namespace ArithmeticFunction

open Nat Finset

/-- **Dedekind psi function.** The Dedekind psi function $\psi$ is the arithmetic function with
values in $\mathbb{N}$ given by $\psi(0) = 0$ and, for $n > 0$,
$$
\psi(n) = \prod_{p^k \parallel n} p^{k-1} (p + 1),
$$
the product running over the primes $p$ dividing $n$, with $p^k$ the exact power of $p$ dividing
$n$.
-/
def dedekindPsi : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p k => p ^ (k - 1) * (p + 1)
  map_zero' := by simp

@[simp]
theorem dedekindPsi_zero : dedekindPsi (0 : ℕ) = 0 := by
  simp [dedekindPsi]

@[simp]
theorem dedekindPsi_one : dedekindPsi (1 : ℕ) = 1 := by
  simp [dedekindPsi, Nat.factorization_one]

/-- **Dedekind psi function as a product over prime powers.** For every natural number $n \ne 0$,
the Dedekind psi function $\psi$ satisfies
$$
\psi(n) = \prod_{p^k \parallel n} p^{k-1} (p + 1),
$$
the product running over the primes $p$ dividing $n$, with $p^k$ the exact power of $p$ dividing
$n$. -/
theorem dedekindPsi_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    dedekindPsi n = n.factorization.prod fun p k => p ^ (k - 1) * (p + 1) := by
  simp [dedekindPsi, hn]

/-- **Dedekind psi function at prime powers.** For every prime $p$ and every natural number
$k > 0$, the Dedekind psi function $\psi$ satisfies $\psi(p^k) = p^{k-1} (p + 1)$. -/
theorem dedekindPsi_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    dedekindPsi (p ^ k) = p ^ (k - 1) * (p + 1) := by
  rw [dedekindPsi_eq_prod_factorization (pow_ne_zero k hp.ne_zero), hp.factorization_pow]
  have hk_ne : k ≠ 0 := Nat.ne_zero_of_lt hk
  have hside :
      (fun (a b : ℕ) => if b = 0 then (1 : ℕ) else a ^ (b - 1) * (a + 1)) p 0 = 1 := by
    simp
  have hcongr :
      (Finsupp.single p k).prod (fun a b => a ^ (b - 1) * (a + 1)) =
        (Finsupp.single p k).prod
          fun a b => if b = 0 then 1 else a ^ (b - 1) * (a + 1) := by
    apply Finsupp.prod_congr
    intro a ha
    have ha_eq : a = p := by
      rw [Finsupp.support_single p hk_ne] at ha
      simpa using ha
    subst a
    simp [hk_ne]
  rw [hcongr, Finsupp.prod_single_index hside]
  simp [hk_ne]

theorem dedekindPsi_prime {p : ℕ} (hp : Nat.Prime p) : dedekindPsi p = p + 1 := by
  simpa only [pow_one, Nat.reduceSubDiff, pow_zero, one_mul] using
    dedekindPsi_prime_pow (k := 1) hp Nat.one_pos

/-- **Multiplicativity of the Dedekind psi function.** The Dedekind psi function $\psi$ is
multiplicative: $\psi(1) = 1$ and $\psi(mn) = \psi(m) \psi(n)$ for all coprime natural numbers
$m$ and $n$. -/
theorem isMultiplicative_dedekindPsi : IsMultiplicative dedekindPsi := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨dedekindPsi_one, fun {m n} hm hn hmn => ?_⟩
  rw [dedekindPsi_eq_prod_factorization hm, dedekindPsi_eq_prod_factorization hn,
    dedekindPsi_eq_prod_factorization (mul_ne_zero hm hn),
    Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

/-- **Cleared-denominator product formula for the Dedekind psi function.** For every natural
number $n \ne 0$, the Dedekind psi function $\psi$ satisfies
$$
\psi(n) \prod_{p \mid n} p = n \prod_{p \mid n} (p + 1),
$$
both products running over the prime divisors $p$ of $n$. -/
theorem dedekindPsi_mul_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    dedekindPsi n * ∏ p ∈ n.primeFactors, p = n * ∏ p ∈ n.primeFactors, (p + 1) := by
  rw [dedekindPsi_eq_prod_factorization hn]
  have hn_prod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    calc
      n = n.factorization.prod fun p k => p ^ k := (Nat.prod_factorization_pow_eq_self hn).symm
      _ = ∏ p ∈ n.factorization.support, p ^ n.factorization p := rfl
      _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by rw [Nat.support_factorization]
  have hpsi_prod : n.factorization.prod (fun p k => p ^ (k - 1) * (p + 1)) =
      ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p + 1)) := by
    calc
      _ = ∏ p ∈ n.factorization.support,
          (p ^ (n.factorization p - 1) * (p + 1)) := rfl
      _ = _ := by rw [Nat.support_factorization]
  rw [hpsi_prod]
  have hkey : (∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p + 1))) *
      (∏ p ∈ n.primeFactors, p) =
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) *
        (∏ p ∈ n.primeFactors, (p + 1)) := by
    rw [← Finset.prod_mul_distrib]
    conv_rhs => rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hmem : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
    have hkpos : 0 < n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem)
    calc
      (p ^ (n.factorization p - 1) * (p + 1)) * p =
          (p ^ (n.factorization p - 1) * p) * (p + 1) := by ac_rfl
      _ = p ^ n.factorization p * (p + 1) := by rw [Nat.pow_pred_mul hkpos]
  rw [hkey, ← hn_prod]

/-- **Product formula for the Dedekind psi function.** For every natural number $n \ne 0$, the
Dedekind psi function $\psi$ satisfies, as an identity of rational numbers,
$$
\psi(n) = n \prod_{p \mid n} \Bigl(1 + \frac{1}{p}\Bigr),
$$
the product running over the prime divisors $p$ of $n$. -/
theorem dedekindPsi_eq_rational_prod {n : ℕ} (hn : n ≠ 0) :
    (dedekindPsi n : ℚ) = (n : ℚ) * ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹) := by
  have hcleared : (dedekindPsi n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) =
      (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) + 1) := by
    simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_add, Nat.cast_one] using
      congrArg (fun x : ℕ => (x : ℚ)) (dedekindPsi_mul_prod_primeFactors hn)
  have hprod_ne : (∏ p ∈ n.primeFactors, (p : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  have hpointwise : ∀ p ∈ n.primeFactors,
      ((p : ℚ) + 1) = (p : ℚ) * (1 + (p : ℚ)⁻¹) := by
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
    rw [mul_add, mul_one, mul_inv_cancel₀ hp0]
  have hprod_eq : ∏ p ∈ n.primeFactors, ((p : ℚ) + 1) =
      (∏ p ∈ n.primeFactors, (p : ℚ)) *
        ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpointwise
  apply mul_left_cancel₀ hprod_ne
  calc
    (∏ p ∈ n.primeFactors, (p : ℚ)) * (dedekindPsi n : ℚ) =
        (dedekindPsi n : ℚ) * ∏ p ∈ n.primeFactors, (p : ℚ) := mul_comm _ _
    _ = (n : ℚ) * ∏ p ∈ n.primeFactors, ((p : ℚ) + 1) := hcleared
    _ = (n : ℚ) * ((∏ p ∈ n.primeFactors, (p : ℚ)) *
        ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹)) := by rw [hprod_eq]
    _ = (∏ p ∈ n.primeFactors, (p : ℚ)) *
        ((n : ℚ) * ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹)) := by ac_rfl

end ArithmeticFunction
