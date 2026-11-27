/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.SplitIfs

/-!
# The twisted B-free indicator convolved with Möbius

This module defines the B-free indicator and proves the support and values of its
coprimality-restricted convolution with the Möbius function.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 6, Equation (23).
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset
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
/-- **The integer $1$ is $B_\kappa$-free.** Let $\kappa$ be a function from the natural numbers
to the natural numbers with $\kappa(p) \ge 1$ for every prime $p$. Then the indicator
$q_{B_\kappa}$ of $B_\kappa$-free integers satisfies $q_{B_\kappa}(1) = 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Equation (12). -/
public theorem bFreeIndicator_one {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) :
    bFreeIndicator κ 1 = 1 := by
  classical
  have h (p : ℕ) (hp : p.Prime) : ¬ p ^ κ p ∣ 1 := by
    intro hd
    have := Nat.dvd_one.mp hd
    have := Nat.pow_le_pow_right hp.pos (hκ p hp)
    simp only [pow_one] at this
    have := hp.two_le
    omega
  change (if 1 ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ 1 then 1 else 0) = 1
  exact ite_eq_left ⟨one_ne_zero, h⟩

private theorem indicator_prime_pow {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    bFreeIndicator κ (p ^ a) = if a < κ p then 1 else 0 := by
  classical
  have h : (∀ q : ℕ, q.Prime → ¬ q ^ κ q ∣ p ^ a) ↔ a < κ p := by
    constructor
    · intro h
      exact Nat.lt_of_not_ge fun ha => h p hp
        ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr ha)
    · intro ha q hq hd
      have hqp : q ∣ p := hq.dvd_of_dvd_pow
        ((dvd_pow_self q (Nat.ne_of_gt (hκ q hq))).trans hd)
      have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      subst q
      exact (Nat.not_le_of_gt ha) ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd)
  have h0 : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  change (if p ^ a ≠ 0 ∧ ∀ q : ℕ, q.Prime → ¬ q ^ κ q ∣ p ^ a then 1 else 0) = _
  simp only [and_iff_right h0, h]

private theorem indicator_mul {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) :
    bFreeIndicator κ (m * n) = bFreeIndicator κ m * bFreeIndicator κ n := by
  classical
  have h : (∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ m * n) ↔
      (∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ m) ∧
        (∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n) := by
    have hd (p : ℕ) (hp : p.Prime) : p ^ κ p ∣ m * n ↔
        p ^ κ p ∣ m ∨ p ^ κ p ∣ n :=
      hmn.isPrimePow_dvd_mul ⟨p, κ p, hp.prime, hκ p hp, rfl⟩
    constructor
    · intro h
      exact ⟨fun p hp hpm => h p hp ((hd p hp).mpr (Or.inl hpm)),
        fun p hp hpn => h p hp ((hd p hp).mpr (Or.inr hpn))⟩
    · rintro ⟨hm, hn⟩ p hp hdvd
      exact ((hd p hp).mp hdvd).elim (hm p hp) (hn p hp)
  change (if m * n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ m * n then 1 else 0) =
    (if m ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ m then 1 else 0) *
      (if n ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ^ κ p ∣ n then 1 else 0)
  simp only [and_iff_right (mul_ne_zero hm hn), and_iff_right hm, and_iff_right hn, h]
  split_ifs <;> simp_all

private noncomputable def twistedIndicator (κ : ℕ → ℕ) (ξ : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n.Coprime ξ then bFreeIndicator κ n else 0, by simp⟩

private theorem twistedIndicator_mult {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) (ξ : ℕ) :
    (twistedIndicator κ ξ).IsMultiplicative := by
  classical
  apply IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [twistedIndicator, bFreeIndicator_one hκ], ?_⟩
  intro m n hm hn hmn
  simp only [twistedIndicator, coe_mk, Nat.coprime_mul_iff_left,
    indicator_mul hκ hm hn hmn]
  split_ifs <;> simp_all

private noncomputable def twistedConvolution (κ : ℕ → ℕ) (ξ : ℕ) : ArithmeticFunction ℤ :=
  twistedIndicator κ ξ * μ

private theorem twistedConvolution_mult {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) (ξ : ℕ) :
    (twistedConvolution κ ξ).IsMultiplicative :=
  (twistedIndicator_mult hκ ξ).mul isMultiplicative_moebius

private theorem twistedConvolution_apply (κ : ℕ → ℕ) (ξ n : ℕ) :
    twistedConvolution κ ξ n =
      ∑ d ∈ n.divisors, (if d.Coprime ξ then bFreeIndicator κ d else 0) * μ (n / d) := by
  classical
  rw [twistedConvolution, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => twistedIndicator κ ξ d * μ e)]
  rfl

private theorem twistedConvolution_prime_pow_succ (κ : ℕ → ℕ) (ξ : ℕ)
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    twistedConvolution κ ξ (p ^ (a + 1)) =
      twistedIndicator κ ξ (p ^ (a + 1)) - twistedIndicator κ ξ (p ^ a) := by
  classical
  have hs (a : ℕ) : ∑ i ∈ range (a + 1), twistedConvolution κ ξ (p ^ i) =
      twistedIndicator κ ξ (p ^ a) := by
    rw [← Nat.sum_divisors_prime_pow hp, ← coe_mul_zeta_apply]
    simp [twistedConvolution, mul_assoc]
  have h := hs (a + 1)
  rw [sum_range_succ, hs a] at h
  exact eq_sub_of_add_eq' h

private theorem twistedConvolution_prime_pow {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) (ξ : ℕ) {p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) :
    twistedConvolution κ ξ (p ^ a) =
      if a = (if p ∣ ξ then 1 else κ p) then -1 else 0 := by
  classical
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  rw [twistedConvolution_prime_pow_succ κ ξ hp]
  by_cases hd : p ∣ ξ
  · have hc : ¬ p.Coprime ξ := (hp.coprime_iff_not_dvd).not.mpr (not_not.mpr hd)
    by_cases hb : b = 0
    · simp [hb, twistedIndicator, hc, bFreeIndicator_one hκ, hd]
    · have hb' : 0 < b := Nat.pos_of_ne_zero hb
      simp [twistedIndicator, Nat.coprime_pow_left_iff (Nat.succ_pos b),
        Nat.coprime_pow_left_iff hb', hc, hd, hb]
  · have hc : p.Coprime ξ := hp.coprime_iff_not_dvd.mpr hd
    simp only [twistedIndicator, coe_mk]
    rw [ite_eq_left (hc.pow_left (b + 1)), ite_eq_left (hc.pow_left b),
      indicator_prime_pow hκ hp, indicator_prime_pow hκ hp, ite_eq_right hd]
    have := hκ p hp
    split_ifs <;> omega

private def kappaPower (κ : ℕ → ℕ) (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => p ^ (κ p * e)

private theorem kappaPower_prime_pow (κ : ℕ → ℕ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    kappaPower κ (p ^ a) = p ^ (κ p * a) := by
  simp [kappaPower, hp.factorization_pow]

private theorem kappaPower_mul (κ : ℕ → ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    kappaPower κ (m * n) = kappaPower κ m * kappaPower κ n := by
  unfold kappaPower
  rw [Nat.factorization_mul_of_coprime hmn]
  exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors _

private theorem kappaPower_coprime (κ : ℕ → ℕ) {n ξ : ℕ} (hn : n.Coprime ξ) :
    (kappaPower κ n).Coprime ξ := by
  rw [kappaPower, Nat.prod_factorization_eq_prod_primeFactors]
  exact Nat.Coprime.prod_left fun p hp =>
    (Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) hn).pow_left _

private theorem prime_coprime_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {p : ℕ} (hp : p.Prime) (hps : p ∉ s) : p.Coprime (∏ q ∈ s, q) := by
  apply Nat.Coprime.prod_right
  intro q hq
  exact (Nat.coprime_primes hp (hs q hq)).mpr fun he => hps (he ▸ hq)

private theorem kappaPower_prod (κ : ℕ → ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    kappaPower κ (∏ p ∈ s, p) = ∏ p ∈ s, p ^ κ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kappaPower]
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self p s)
    have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    rw [prod_insert hp, kappaPower_mul κ (prime_coprime_prod hsp hpp hp), ih hsp,
      prod_insert hp]
    congr 1
    simpa only [pow_one, mul_one] using kappaPower_prime_pow κ hpp 1

private theorem prime_prod_dvd {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (ξ : ℕ)
    (hd : ∀ p ∈ s, p ∣ ξ) : (∏ p ∈ s, p) ∣ ξ :=
  Finset.prod_dvd_of_isRelPrime (s := id) (fun p hp q hq hpq =>
    Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)) hd

private theorem twistedConvolution_of_dvd {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {ℓ ξ : ℕ} (hℓ : ℓ ∣ ξ) :
    twistedConvolution κ ξ ℓ = μ ℓ := by
  classical
  by_cases h0 : ℓ = 0
  · simp [h0]
  rw [(twistedConvolution_mult hκ ξ).multiplicative_factorization _ h0,
    isMultiplicative_moebius.multiplicative_factorization _ h0]
  apply Finsupp.prod_congr
  intro p hp
  have hp' : p ∈ ℓ.primeFactors := by simpa only [Nat.support_factorization] using hp
  have hpp := Nat.prime_of_mem_primeFactors hp'
  have he := hpp.factorization_pos_of_dvd h0 (Nat.dvd_of_mem_primeFactors hp')
  have hd := (Nat.dvd_of_mem_primeFactors hp').trans hℓ
  rw [twistedConvolution_prime_pow hκ ξ hpp he, ite_eq_left hd,
    moebius_apply_prime_pow hpp he.ne']

private theorem twistedConvolution_kappaPower {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {r ξ : ℕ} (hr : r.Coprime ξ) (hr0 : r ≠ 0) :
    twistedConvolution κ ξ (kappaPower κ r) = μ r := by
  classical
  have hmult (m n : ℕ) (hmn : m.Coprime n) :
      twistedConvolution κ ξ (kappaPower κ (m * n)) =
        twistedConvolution κ ξ (kappaPower κ m) *
          twistedConvolution κ ξ (kappaPower κ n) := by
    rw [kappaPower_mul κ hmn]
    exact (twistedConvolution_mult hκ ξ).map_mul_of_coprime
      (kappaPower_coprime κ (kappaPower_coprime κ hmn).symm).symm
  rw [Nat.multiplicative_factorization (fun n => twistedConvolution κ ξ (kappaPower κ n))
    hmult (by simp [kappaPower, (twistedConvolution_mult hκ ξ).map_one]) hr0,
    isMultiplicative_moebius.multiplicative_factorization _ hr0]
  apply Finsupp.prod_congr
  intro p hp
  have hp' : p ∈ r.primeFactors := by simpa only [Nat.support_factorization] using hp
  have hpp := Nat.prime_of_mem_primeFactors hp'
  have he := hpp.factorization_pos_of_dvd hr0 (Nat.dvd_of_mem_primeFactors hp')
  have hk : 0 < κ p := hκ p hpp
  have hd : ¬ p ∣ ξ := hpp.coprime_iff_not_dvd.mp
    (Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp') hr)
  rw [kappaPower_prime_pow κ hpp, twistedConvolution_prime_pow hκ ξ hpp (Nat.mul_pos hk he),
    ite_eq_right hd, moebius_apply_prime_pow hpp he.ne']
  have h : κ p * r.factorization p = κ p ↔ r.factorization p = 1 := by
    constructor
    · intro h
      apply mul_left_cancel₀ hk.ne'
      simpa only [mul_one] using h
    · rintro h
      simp only [h, mul_one]
  simp only [h]

/-- **The $B_\kappa$-free indicator twisted by the principal character, convolved with $\mu$.**
Let $\kappa$ be a function from the natural numbers to the natural numbers with $\kappa(p) \ge 1$
for every prime $p$, let $\xi$ be a natural number, let $q_{B_\kappa}$ be the indicator of
$B_\kappa$-free integers and let $\mu$ be the Möbius function. Put $w(d) = q_{B_\kappa}(d)$ if
$\gcd(d, \xi) = 1$ and $w(d) = 0$ otherwise, so that $w = q_{B_\kappa} \chi_\xi$ with $\chi_\xi$
the principal character modulo $\xi$, and let $(w * \mu)(n) = \sum_{d \mid n} w(d) \mu(n/d)$, the
sum running over the positive divisors $d$ of $n$ (it is empty for $n = 0$). For $r \ge 1$ with
prime factorization $r = \prod_p p^{e_p}$ write $r^\kappa = \prod_p p^{\kappa(p) e_p}$, and set
$0^\kappa = 1$. Then for every natural number $n$ with $(w * \mu)(n) \ne 0$ there are natural
numbers $\ell$ and $r$ with $\ell \mid \xi$, $\gcd(r, \xi) = 1$ and $n = \ell r^\kappa$. Moreover,
for all natural numbers $\ell$ and $r$ with $\ell \mid \xi$, $\gcd(r, \xi) = 1$ and $r \ge 1$,
$(w * \mu)(\ell r^\kappa) = \mu(\ell) \mu(r)$.

The hypothesis $r \ge 1$ in the evaluation is needed: for $r = 0$ the formula is false. No
positivity of $\xi$ is assumed.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 6, Equation (23) (`integers-2024-A75-lem-6`). -/
public theorem bFreeCoprimeIndicator_mul_moebius {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) (ξ : ℕ) :
    (∀ n : ℕ, ∑ d ∈ n.divisors, (if d.Coprime ξ then bFreeIndicator κ d else 0) * μ (n / d) ≠ 0 →
        ∃ ℓ r : ℕ, ℓ ∣ ξ ∧ r.Coprime ξ ∧ n = ℓ * r.factorization.prod fun p e => p ^ (κ p * e)) ∧
      ∀ ℓ r : ℕ, ℓ ∣ ξ → r.Coprime ξ → 0 < r →
        ∑ d ∈ (ℓ * r.factorization.prod fun p e => p ^ (κ p * e)).divisors,
            (if d.Coprime ξ then bFreeIndicator κ d else 0) *
              μ ((ℓ * r.factorization.prod fun p e => p ^ (κ p * e)) / d) = μ ℓ * μ r := by
  classical
  constructor
  · intro n hn
    have hg : twistedConvolution κ ξ n ≠ 0 := by
      simpa only [twistedConvolution_apply] using hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hg ArithmeticFunction.map_zero
    rw [(twistedConvolution_mult hκ ξ).multiplicative_factorization _ hn0,
      Nat.prod_factorization_eq_prod_primeFactors] at hg
    have he (p : ℕ) (hp : p ∈ n.primeFactors) :
        n.factorization p = if p ∣ ξ then 1 else κ p := by
      have hpp := Nat.prime_of_mem_primeFactors hp
      have ha := hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
      have h := prod_ne_zero_iff.mp hg p hp
      rw [twistedConvolution_prime_pow hκ ξ hpp ha] at h
      by_contra hne
      exact h (ite_eq_right hne)
    let s := n.primeFactors.filter (fun p => p ∣ ξ)
    let t := n.primeFactors.filter (fun p => ¬ p ∣ ξ)
    have hs : ∀ p ∈ s, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have ht : ∀ p ∈ t, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    refine ⟨∏ p ∈ s, p, ∏ p ∈ t, p,
      prime_prod_dvd hs ξ (fun p hp => (mem_filter.mp hp).2), ?_, ?_⟩
    · exact Nat.Coprime.prod_left fun p hp =>
        (ht p hp).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2
    · change n = (∏ p ∈ s, p) * kappaPower κ (∏ p ∈ t, p)
      rw [kappaPower_prod κ ht]
      calc
        n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
          Nat.prod_primeFactors_pow_factorization hn0
        _ = (∏ p ∈ s, p ^ n.factorization p) *
            ∏ p ∈ t, p ^ n.factorization p :=
          (prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ∣ ξ) _).symm
        _ = _ := by
          congr 1
          · apply prod_congr rfl
            intro p hp
            rw [he p (mem_filter.mp hp).1, ite_eq_left (mem_filter.mp hp).2, pow_one]
          · apply prod_congr rfl
            intro p hp
            rw [he p (mem_filter.mp hp).1, ite_eq_right (mem_filter.mp hp).2]
  · intro ℓ r hℓ hr hr0
    rw [← twistedConvolution_apply]
    change twistedConvolution κ ξ (ℓ * kappaPower κ r) = μ ℓ * μ r
    have hc : ℓ.Coprime (kappaPower κ r) :=
      (Nat.Coprime.of_dvd_right hℓ (kappaPower_coprime κ hr)).symm
    rw [(twistedConvolution_mult hκ ξ).map_mul_of_coprime hc,
      twistedConvolution_of_dvd hκ hℓ, twistedConvolution_kappaPower hκ hr hr0.ne']

end

end MetaMathlibExt
