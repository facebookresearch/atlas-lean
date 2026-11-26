/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Dirichlet convolution of the B-free indicator with the Möbius function

The convolution is evaluated from the prime exponents of a positive integer in
`bFreeIndicator_mul_moebius_apply`.
-/

namespace MetaMathlibExt

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

@[expose] public section

open scoped Classical in
/-- **Indicator of $B_\kappa$-free integers.** Let $\kappa$ be a function from the natural numbers
to the natural numbers (only its values $\kappa(p)$ at primes $p$ matter) and let $B_\kappa$ be
the set of prime powers $p^{\kappa(p)}$. A natural number $n$ is $B_\kappa$-free if $n \ge 1$ and
no $p^{\kappa(p)}$ with $p$ prime divides $n$. The indicator $q_{B_\kappa}$ is the integer-valued
arithmetic function with $q_{B_\kappa}(n) = 1$ if $n$ is $B_\kappa$-free and
$q_{B_\kappa}(n) = 0$ otherwise.

The paper indexes the exponents by the position of the prime ($b_i = p_i^{\kappa_i}$); here
$\kappa$ is indexed by the prime itself. For constant $\kappa = k$ this is the indicator $q_k$ of
$k$-free integers.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equations (2), (11), (12). -/
public noncomputable def bFreeIndicator (κ : ℕ → ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n then 1 else 0, by simp⟩

open scoped Classical in
/-- **Values of the $B_\kappa$-free indicator.** Let $\kappa$ be a function from the natural
numbers to the natural numbers. For every natural number $n$, the indicator $q_{B_\kappa}$ of
$B_\kappa$-free integers satisfies $q_{B_\kappa}(n) = 1$ if $n \ne 0$ and no $p^{\kappa(p)}$ with
$p$ prime divides $n$, and $q_{B_\kappa}(n) = 0$ otherwise.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equations (11), (12). -/
public theorem bFreeIndicator_apply (κ : ℕ → ℕ) (n : ℕ) :
    bFreeIndicator κ n = if n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n then 1 else 0 :=
  rfl

open scoped Classical in
/-- **The integer $1$ is $B_\kappa$-free.** Let $\kappa$ be a function from the natural numbers
to the natural numbers with $\kappa(p) \ge 1$ for every prime $p$. Then the indicator
$q_{B_\kappa}$ of $B_\kappa$-free integers satisfies $q_{B_\kappa}(1) = 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equation (12). -/
public theorem bFreeIndicator_one {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) :
    bFreeIndicator κ 1 = 1 := by
  have h : ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ 1 := by
    intro p hp hdvd
    have h1 : p ^ κ p = 1 := Nat.dvd_one.mp hdvd
    have h2 : p ^ 1 ≤ p ^ κ p := Nat.pow_le_pow_right hp.pos (hκ p hp)
    rw [pow_one] at h2
    have h3 := hp.two_le
    omega
  rw [bFreeIndicator_apply, ite_eq_left_iff]
  intro hc
  exact absurd ⟨one_ne_zero, h⟩ hc

open scoped Classical in
/-- **The prime power $p^{\kappa(p)}$ is not $B_\kappa$-free.** Let $\kappa$ be a function from
the natural numbers to the natural numbers and let $p$ be a prime. Then the indicator
$q_{B_\kappa}$ of $B_\kappa$-free integers satisfies $q_{B_\kappa}(p^{\kappa(p)}) = 0$.

No positivity of $\kappa(p)$ is assumed; for $\kappa(p) = 0$ the statement is
$q_{B_\kappa}(1) = 0$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equation (12). -/
public theorem bFreeIndicator_prime_pow {κ : ℕ → ℕ} {p : ℕ} (hp : p.Prime) :
    bFreeIndicator κ (p ^ κ p) = 0 := by
  have : ¬ (p ^ κ p ≠ 0 ∧ ∀ q : ℕ, q.Prime → ¬ q ^ κ q ∣ p ^ κ p) := by
    rintro ⟨-, h⟩
    exact h p hp dvd_rfl
  rw [bFreeIndicator_apply, ite_eq_right_iff]
  intro hc
  exact absurd hc this

namespace bFreeIndicator

private theorem isMultiplicative {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) :
    (bFreeIndicator κ).IsMultiplicative := by
  classical
  refine IsMultiplicative.iff_ne_zero.mpr ⟨bFreeIndicator_one hκ, ?_⟩
  intro m n hm hn hmn
  have hd (p : ℕ) (hp : p.Prime) :
      p ^ κ p ∣ m * n ↔ p ^ κ p ∣ m ∨ p ^ κ p ∣ n :=
    hmn.isPrimePow_dvd_mul (hp.isPrimePow.pow (Nat.ne_of_gt (hκ p hp)))
  simp +contextual [bFreeIndicator_apply, hm, hn, hd, not_or, forall_and]
  split_ifs <;> tauto

private theorem apply_prime_pow {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    bFreeIndicator κ (p ^ e) = if e < κ p then 1 else 0 := by
  classical
  have hne := pow_ne_zero e hp.ne_zero
  rw [bFreeIndicator_apply]
  congr 1
  apply propext
  constructor
  · intro h
    exact lt_of_not_ge fun hle => h.2 p hp (pow_dvd_pow p hle)
  · intro he
    refine ⟨hne, fun q hq => ?_⟩
    rw [hq.pow_dvd_iff_le_factorization hne, hp.factorization_pow]
    by_cases h : p = q
    · subst q
      simpa using he
    · simpa [Finsupp.single_apply, h] using Nat.ne_of_gt (hκ q hq)

private theorem mul_moebius_prime_pow {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p)
    {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    (bFreeIndicator κ * μ) (p ^ e) =
      if κ p ∣ e then μ (p ^ (e / κ p)) else 0 := by
  -- Inverting the divisor sum leaves the difference of two consecutive indicator values.
  let g := bFreeIndicator κ * μ
  have hsum (j : ℕ) :
      ∑ i ∈ Finset.range (j + 1), g (p ^ i) = bFreeIndicator κ (p ^ j) := by
    rw [← Nat.sum_divisors_prime_pow hp, ← coe_mul_zeta_apply]
    simp [g, mul_assoc]
  have hlocal : g (p ^ e) = if e = κ p then -1 else 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    have h := hsum (j + 1)
    rw [Finset.sum_range_succ, hsum, apply_prime_pow hκ hp, apply_prime_pow hκ hp] at h
    change g (p ^ (j + 1)) = if j + 1 = κ p then -1 else 0
    split_ifs at h ⊢ <;> omega
  change g (p ^ e) = _
  rw [hlocal]
  by_cases hd : κ p ∣ e
  · have hpos := Nat.div_pos (Nat.le_of_dvd he hd) (hκ p hp)
    rw [ite_eq_left hd, moebius_apply_prime_pow hp hpos.ne']
    have hiff : e / κ p = 1 ↔ e = κ p := by
      constructor
      · intro h
        simpa [h] using (Nat.div_mul_cancel hd).symm
      · rintro rfl
        exact Nat.div_self (hκ p hp)
    simp only [hiff]
  · simp [hd, show e ≠ κ p from fun h => hd (h ▸ dvd_rfl)]

end bFreeIndicator

open scoped Classical in
/-- **The $B_\kappa$-free indicator convolved with the Möbius function.** Let $\kappa$ be a
function from the natural numbers to the natural numbers with $\kappa(p) \ge 1$ for every prime
$p$, let $q_{B_\kappa}$ be the indicator of $B_\kappa$-free integers, let $\mu$ be the Möbius
function and let $*$ denote Dirichlet convolution. Let $n \ge 1$ be a natural number with prime
factorization $n = \prod_p p^{e_p}$. If $\kappa(p)$ divides $e_p$ for every prime $p$, then
$(q_{B_\kappa} * \mu)(n) = \mu(n^{1/\kappa})$, where $n^{1/\kappa} = \prod_p p^{e_p/\kappa(p)}$;
otherwise $(q_{B_\kappa} * \mu)(n) = 0$.

The source indexes the exponents by the position of the prime ($\kappa_i$ for the $i$-th prime
$p_i$) and requires $b_i = p_i^{\kappa_i} > 1$, which is the hypothesis $\kappa(p) \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 5, Equation (22) (`integers-2024-A75-lem-5`). -/
public theorem bFreeIndicator_mul_moebius_apply {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {n : ℕ} (hn : 1 ≤ n) :
    (bFreeIndicator κ * μ) n =
      if ∀ p : ℕ, κ p ∣ n.factorization p then
        μ (n.factorization.prod fun p e => p ^ (e / κ p))
      else 0 := by
  classical
  have hmult := (bFreeIndicator.isMultiplicative hκ).mul isMultiplicative_moebius
  rw [hmult.multiplicative_factorization _ (by omega : n ≠ 0)]
  simp only [Finsupp.prod, Nat.support_factorization]
  split_ifs with hall
  · rw [isMultiplicative_moebius.map_prod]
    · apply Finset.prod_congr rfl
      intro p hp
      have he : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
      rw [bFreeIndicator.mul_moebius_prime_pow hκ (Nat.prime_of_mem_primeFactors hp) he,
        ite_eq_left (hall p)]
    · intro p hp q hq hne
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hne)
  · obtain ⟨p, hp⟩ := Classical.not_forall.mp hall
    have he : n.factorization p ≠ 0 := fun h => hp (h ▸ dvd_zero _)
    have hmem : p ∈ n.primeFactors := Finsupp.mem_support_iff.mpr he
    apply Finset.prod_eq_zero hmem
    rw [bFreeIndicator.mul_moebius_prime_pow hκ (Nat.prime_of_mem_primeFactors hmem)
      (Nat.pos_of_ne_zero he), ite_eq_right hp]

end

end MetaMathlibExt
