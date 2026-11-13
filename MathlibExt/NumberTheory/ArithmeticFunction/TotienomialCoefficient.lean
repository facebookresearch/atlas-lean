/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.Combinatorics.Enumerative.TotienomialCoefficient
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Totienomial coefficients: integrality and prime factorization -/

/-- Floor division is superadditive: separate divisions round down at least as much. -/
private theorem div_add_le_div (a b d : ℕ) : a / d + b / d ≤ (a + b) / d := by
  rcases eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.le_div_iff_mul_le hd]
    calc (a / d + b / d) * d = a / d * d + b / d * d := by ring
    _ ≤ a + b := Nat.add_le_add (Nat.div_mul_le_self a d) (Nat.div_mul_le_self b d)

/-- The product of `1, .., K` is `K !`. -/
private theorem prod_Icc_one_eq_factorial (K : ℕ) : ∏ i ∈ Finset.Icc 1 K, i = K.factorial := by
  induction K with
  | zero => simp
  | succ K ih =>
    show ∏ i ∈ Finset.Icc 1 (K + 1), i = (K + 1).factorial
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K + 1), ih, Nat.factorial_succ, mul_comm]

/-- Double counting: collecting `g p` over prime factors of each `i ≤ K` groups by prime,
each prime `p` occurring for the `K / p` multiples of `p`. -/
private theorem prod_primeFactors_swap (g : ℕ → ℕ) (K : ℕ) :
    (∏ i ∈ Finset.Icc 1 K, ∏ p ∈ i.primeFactors, g p)
      = ∏ p ∈ Nat.primesLE K, g p ^ (K / p) := by
  set S : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.Icc 1 K).sigma (fun i => i.primeFactors) with hS
  have hsub : ∀ i : ℕ, i ∈ Finset.Icc 1 K → ∀ p : ℕ,
      p ∈ i.primeFactors → p ∈ Nat.primesLE K := by
    intro i hi p hp
    rw [Nat.mem_primesLE]
    exact ⟨le_trans (Nat.le_of_mem_primeFactors hp) (Finset.mem_Icc.mp hi).2,
      (Nat.mem_primeFactors.mp hp).1⟩
  have hA : (∏ x ∈ S, g x.2) = ∏ i ∈ Finset.Icc 1 K, ∏ p ∈ i.primeFactors, g p := by
    rw [hS]
    exact Finset.prod_sigma _ _ _
  have hfib : ∀ p : ℕ, p ∈ Nat.primesLE K →
      ∏ x ∈ S.filter (fun x => x.2 = p), g x.2 = g p ^ (K / p) := by
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    have him : S.filter (fun x => x.2 = p)
        = ((Finset.Icc 1 K).filter (fun i => p ∣ i)).image
          (fun i => (⟨i, p⟩ : Sigma fun _ : ℕ => ℕ)) := by
      rw [hS]
      ext x
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h3⟩, hx2⟩
        cases hx2
        refine ⟨x.1, ⟨h1, (Nat.mem_primeFactors.mp h3).2.1⟩, rfl⟩
      · rintro ⟨i, ⟨hiIcc, hidvd⟩, hix⟩
        have e1 : x.1 = i := by cases hix; rfl
        have e2 : x.2 = p := by cases hix; rfl
        rw [e1, e2]
        refine ⟨⟨hiIcc, ?_⟩, rfl⟩
        rw [Nat.mem_primeFactors]
        have h1i : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
        exact ⟨hpp, hidvd, by omega⟩
    have hconst : ∏ i ∈ (Finset.Icc 1 K).filter (fun i => p ∣ i),
          g (⟨i, p⟩ : Sigma fun _ : ℕ => ℕ).2
        = ∏ _i ∈ (Finset.Icc 1 K).filter (fun i => p ∣ i), g p :=
      Finset.prod_congr rfl (fun i _ => rfl)
    have hcard : ((Finset.Icc 1 K).filter (fun i => p ∣ i)).card = K / p := by
      have heq : Finset.Icc 1 K = Finset.Ioc 0 K := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [heq]
      exact Nat.Ioc_filter_dvd_card_eq_div K p
    rw [him, Finset.prod_image (by intro a _ b _ h; simpa using h), hconst,
      Finset.prod_const, hcard]
  have hmap : ∀ x : Sigma fun _ : ℕ => ℕ,
      x ∈ (Finset.Icc 1 K).sigma (fun i => i.primeFactors) → x.2 ∈ Nat.primesLE K := by
    intro x hx
    exact hsub x.1 (Finset.mem_sigma.mp hx).1 x.2 (Finset.mem_sigma.mp hx).2
  have hB : (∏ p ∈ Nat.primesLE K, ∏ x ∈ S.filter (fun x => x.2 = p), g x.2)
      = ∏ x ∈ S, g x.2 := by
    rw [hS]
    exact Finset.prod_fiberwise_of_maps_to hmap _
  rw [← hA, ← hB]
  apply Finset.prod_congr rfl
  intro p hp
  exact hfib p hp

/-- Per-index identity: `φ i` times the primes dividing `i` equals `i` times `q - 1`
over the same primes. -/
private theorem totient_mul_prod_primeFactors (i : ℕ) (hi : 0 < i) :
    i.totient * ∏ p ∈ i.primeFactors, p = i * ∏ p ∈ i.primeFactors, (p - 1) := by
  have hne : i ≠ 0 := ne_of_gt hi
  have htot := Nat.totient_eq_prod_factorization hne
  have hself := Nat.prod_factorization_pow_eq_self hne
  have bridge : ∀ gg : ℕ → ℕ → ℕ,
      i.factorization.prod gg = ∏ p ∈ i.primeFactors, gg p (i.factorization p) := by
    intro gg
    calc i.factorization.prod gg
        = ∏ a ∈ i.factorization.support, gg a (i.factorization a) := rfl
      _ = ∏ p ∈ i.primeFactors, gg p (i.factorization p) := by
          rw [Nat.support_factorization]
  simp only [bridge] at htot hself
  have mid : (∏ p ∈ i.primeFactors, (p ^ (i.factorization p - 1) * (p - 1)))
        * ∏ p ∈ i.primeFactors, p
      = (∏ p ∈ i.primeFactors, p ^ i.factorization p)
        * ∏ p ∈ i.primeFactors, (p - 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have he : i.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hp
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 1 ≤ i.factorization p by omega)
    have hk1 : i.factorization p - 1 = k := by omega
    have hk2 : i.factorization p = k + 1 := by omega
    rw [hk1, hk2, pow_succ]
    ring
  rw [← htot, hself] at mid
  exact mid

/-- Combined identity: the product of `φ` over `1, .., K` times prime powers
equals `K !` times the corresponding `p - 1` powers. -/
private theorem prod_totient_mul_pow (K : ℕ) :
    (∏ i ∈ Finset.Icc 1 K, i.totient) * ∏ p ∈ Nat.primesLE K, p ^ (K / p)
      = K.factorial * ∏ p ∈ Nat.primesLE K, (p - 1) ^ (K / p) := by
  have per : ∀ i ∈ Finset.Icc 1 K,
      i.totient * ∏ p ∈ i.primeFactors, p = i * ∏ p ∈ i.primeFactors, (p - 1) := by
    intro i hi
    exact totient_mul_prod_primeFactors i (Finset.mem_Icc.mp hi).1
  have hcongr := Finset.prod_congr rfl per
  simp only [Finset.prod_mul_distrib, prod_primeFactors_swap] at hcongr
  rw [prod_Icc_one_eq_factorial] at hcongr
  exact hcongr

/-- A product over `primesLE K` extends to `primesLE N` when the extra factors are `1`. -/
private theorem prod_primesLE_extend (F : ℕ → ℕ) {K N : ℕ} (h : K ≤ N)
    (hvan : ∀ p ∈ Nat.primesLE N, p ∉ Nat.primesLE K → F p = 1) :
    ∏ p ∈ Nat.primesLE K, F p = ∏ p ∈ Nat.primesLE N, F p :=
  Finset.prod_subset (Nat.primesLE_mono h) (fun p hp hpn => hvan p hp hpn)

/-- Legendre-type lower bound: the `p`-adic valuation of `C(n+m, n)` dominates the
first-order digit carry `(n+m)/p - n/p - m/p`. -/
private theorem legendre_le (n m p : ℕ) (hp : Nat.Prime p) :
    (n + m) / p - n / p - m / p ≤ Nat.factorization (Nat.choose (n + m) n) p := by
  have hlog : ∀ K : ℕ, K ≤ n + m → Nat.log p K < n + m + 1 := by
    intro K hK
    exact lt_of_le_of_lt (le_trans (Nat.log_le_self p K) hK) (Nat.lt_succ_self _)
  have fN := Nat.factorization_factorial hp (hlog (n + m) le_rfl)
  have fn := Nat.factorization_factorial hp (hlog n (Nat.le_add_right n m))
  have fm := Nat.factorization_factorial hp (hlog m (Nat.le_add_left m n))
  have hCne : Nat.choose (n + m) n ≠ 0 :=
    ne_of_gt (Nat.choose_pos (Nat.le_add_right n m))
  have hCeq : Nat.choose (n + m) n * (n.factorial * m.factorial) = (n + m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n m)
    rw [Nat.add_sub_cancel_left, mul_assoc] at h
    exact h
  have hfact : (Nat.choose (n + m) n).factorization p
        + (n.factorial.factorization p + m.factorial.factorization p)
      = (n + m).factorial.factorization p := by
    have h2 := congrArg (fun q : ℕ => q.factorization p) hCeq
    simp only [Nat.factorization_mul hCne
      (mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero m)),
      Nat.factorization_mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero m),
      Finsupp.add_apply] at h2
    omega
  have hcast : ((Nat.factorization (Nat.choose (n + m) n) p : ℕ) : ℤ)
        = (((n + m).factorial.factorization p : ℕ) : ℤ)
          - (((n.factorial.factorization p : ℕ)) : ℤ)
          - (((m.factorial.factorization p : ℕ)) : ℤ) := by
    have hle : n.factorial.factorization p + m.factorial.factorization p
        ≤ (n + m).factorial.factorization p := by omega
    rw [show (Nat.choose (n + m) n).factorization p
      = (n + m).factorial.factorization p - n.factorial.factorization p
        - m.factorial.factorization p by omega,
      Nat.sub_sub, Nat.cast_sub hle, Nat.cast_add, sub_sub]
  have key : ((Nat.factorization (Nat.choose (n + m) n) p : ℕ) : ℤ)
      = ∑ i ∈ Finset.Ico 1 (n + m + 1),
        (((((n + m) / p ^ i : ℕ)) : ℤ) - ((((n / p ^ i : ℕ))) : ℤ)
          - ((((m / p ^ i : ℕ))) : ℤ)) := by
    rw [hcast, fN, fn, fm, Nat.cast_sum, Nat.cast_sum, Nat.cast_sum,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.Ico 1 (n + m + 1),
      ((0 : ℤ) ≤ ((((n + m) / p ^ i : ℕ)) : ℤ) - ((((n / p ^ i : ℕ))) : ℤ)
        - ((((m / p ^ i : ℕ))) : ℤ)) := by
    intro i _
    have h : n / p ^ i + m / p ^ i ≤ (n + m) / p ^ i := div_add_le_div n m (p ^ i)
    have h1 : ((((n / p ^ i : ℕ))) : ℤ) + ((((m / p ^ i : ℕ))) : ℤ)
        ≤ ((((n + m) / p ^ i : ℕ)) : ℤ) := by exact_mod_cast h
    linarith
  by_cases ha : (n + m) / p - n / p - m / p = 0
  case pos =>
    rw [ha]
    exact Nat.zero_le _
  case neg =>
    have h1mem : (1 : ℕ) ∈ Finset.Ico 1 (n + m + 1) := by
      rw [Finset.mem_Ico]
      refine ⟨le_rfl, ?_⟩
      have h1 : 1 ≤ (n + m) / p := by
        have hsub : (n + m) / p - n / p - m / p ≤ (n + m) / p :=
          le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
        omega
      have hpm : p ≤ n + m := by
        calc p = p * 1 := (mul_one p).symm
          _ ≤ p * ((n + m) / p) := by gcongr
          _ ≤ n + m := by
            rw [mul_comm]
            exact Nat.div_mul_le_self _ _
      have hp2 := hp.two_le
      omega
    have hsingle : ((((n + m) / p ^ 1 : ℕ)) : ℤ) - ((((n / p ^ 1 : ℕ))) : ℤ)
          - ((((m / p ^ 1 : ℕ))) : ℤ)
        ≤ ∑ i ∈ Finset.Ico 1 (n + m + 1),
          (((((n + m) / p ^ i : ℕ)) : ℤ) - ((((n / p ^ i : ℕ))) : ℤ)
            - ((((m / p ^ i : ℕ))) : ℤ)) :=
      Finset.single_le_sum hterm h1mem
    rw [pow_one] at hsingle
    have hcast1 : ((((n + m) / p - n / p - m / p : ℕ)) : ℤ)
        = ((((n + m) / p : ℕ)) : ℤ) - ((((n / p : ℕ))) : ℤ)
          - ((((m / p : ℕ))) : ℤ) := by
      have hle : n / p + m / p ≤ (n + m) / p := div_add_le_div n m p
      rw [Nat.sub_sub, Nat.cast_sub hle, Nat.cast_add, sub_sub]
    apply Int.ofNat_le.mp
    rw [hcast1, key]
    exact hsingle

/--
**Integrality and prime factorization of totienomial coefficients.** For all natural numbers
$n$ and $m$, the totienomial coefficient $\binom{n+m}{n}_\varphi$ of Euler's totient function
$\varphi$ is a natural number, namely
$$\binom{n+m}{n}_\varphi = \prod_{p \le n+m} (p-1)^{c_p} \, p^{v_p(\binom{n+m}{n}) - c_p},$$
where the product runs over the primes $p \le n+m$, $\binom{n+m}{n}$ is the ordinary binomial
coefficient, $v_p$ is the $p$-adic valuation and
$c_p = \lfloor (n+m)/p \rfloor - \lfloor n/p \rfloor - \lfloor m/p \rfloor$.

Both exponents are natural numbers, since $\lfloor n/p \rfloor + \lfloor m/p \rfloor \le
\lfloor (n+m)/p \rfloor$ and $c_p \le v_p(\binom{n+m}{n})$.

Proves `Wanted` entry `totienomial_integral_factorization`.

Source: Tom Edgar and Michael Z. Spivey, "Multiplicative Functions, Generalized Binomial Coefficients, and Generalized Catalan Numbers", Journal of Integer Sequences 19 (2016), Article 16.1.6, Corollary `totcor`, lines 244-249, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex>.
-/
theorem totienomial_integral_factorization (n m : ℕ) :
    ∃ N : ℕ,
      totienomialCoefficient n m = (N : ℚ) ∧
      N = ∏ p ∈ Nat.primesLE (n + m),
        ((p - 1) ^ ((n + m) / p - n / p - m / p) *
          p ^ (Nat.factorization (Nat.choose (n + m) n) p -
            ((n + m) / p - n / p - m / p))) := by
  have htot : totienomialCoefficient n m
      = ((∏ i ∈ Finset.Icc 1 (n + m), i.totient : ℕ) : ℚ)
        / ((((∏ i ∈ Finset.Icc 1 n, i.totient : ℕ)) : ℚ)
          * ((((∏ i ∈ Finset.Icc 1 m, i.totient : ℕ))) : ℚ)) := rfl
  have keyN := prod_totient_mul_pow (n + m)
  have extn1 : ∏ p ∈ Nat.primesLE n, p ^ (n / p)
      = ∏ p ∈ Nat.primesLE (n + m), p ^ (n / p) := by
    refine prod_primesLE_extend _ (Nat.le_add_right n m) ?_
    intro p hp hpn
    show p ^ (n / p) = 1
    have hle : n < p :=
      lt_of_not_ge (fun hle => hpn (Nat.mem_primesLE.mpr ⟨hle, (Nat.mem_primesLE.mp hp).2⟩))
    rw [Nat.div_eq_of_lt hle, pow_zero]
  have extn2 : ∏ p ∈ Nat.primesLE n, (p - 1) ^ (n / p)
      = ∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p) := by
    refine prod_primesLE_extend _ (Nat.le_add_right n m) ?_
    intro p hp hpn
    show (p - 1) ^ (n / p) = 1
    have hle : n < p :=
      lt_of_not_ge (fun hle => hpn (Nat.mem_primesLE.mpr ⟨hle, (Nat.mem_primesLE.mp hp).2⟩))
    rw [Nat.div_eq_of_lt hle, pow_zero]
  have extm1 : ∏ p ∈ Nat.primesLE m, p ^ (m / p)
      = ∏ p ∈ Nat.primesLE (n + m), p ^ (m / p) := by
    refine prod_primesLE_extend _ (Nat.le_add_left m n) ?_
    intro p hp hpn
    show p ^ (m / p) = 1
    have hle : m < p :=
      lt_of_not_ge (fun hle => hpn (Nat.mem_primesLE.mpr ⟨hle, (Nat.mem_primesLE.mp hp).2⟩))
    rw [Nat.div_eq_of_lt hle, pow_zero]
  have extm2 : ∏ p ∈ Nat.primesLE m, (p - 1) ^ (m / p)
      = ∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p) := by
    refine prod_primesLE_extend _ (Nat.le_add_left m n) ?_
    intro p hp hpn
    show (p - 1) ^ (m / p) = 1
    have hle : m < p :=
      lt_of_not_ge (fun hle => hpn (Nat.mem_primesLE.mpr ⟨hle, (Nat.mem_primesLE.mp hp).2⟩))
    rw [Nat.div_eq_of_lt hle, pow_zero]
  have keyn : (∏ i ∈ Finset.Icc 1 n, i.totient) * ∏ p ∈ Nat.primesLE (n + m), p ^ (n / p)
      = n.factorial * ∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p) := by
    have h := prod_totient_mul_pow n
    rwa [extn1, extn2] at h
  have keym : (∏ i ∈ Finset.Icc 1 m, i.totient) * ∏ p ∈ Nat.primesLE (n + m), p ^ (m / p)
      = m.factorial * ∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p) := by
    have h := prod_totient_mul_pow m
    rwa [extm1, extm2] at h
  have hexp : ∀ p : ℕ, (n + m) / p
      = n / p + m / p + ((n + m) / p - n / p - m / p) := by
    intro p
    rw [Nat.sub_sub]
    exact (Nat.add_sub_cancel' (div_add_le_div n m p)).symm
  have hQsplit : ∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ ((n + m) / p)
      = (∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p)) *
        ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p)) *
          ∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ ((n + m) / p - n / p - m / p)) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    nth_rewrite 1 [hexp p]
    rw [pow_add, pow_add, mul_assoc]
  have hPsplit : ∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p)
      = (∏ p ∈ Nat.primesLE (n + m), p ^ (n / p)) *
        ((∏ p ∈ Nat.primesLE (n + m), p ^ (m / p)) *
          ∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p - n / p - m / p)) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    nth_rewrite 1 [hexp p]
    rw [pow_add, pow_add, mul_assoc]
  have hCeq : Nat.choose (n + m) n * n.factorial * m.factorial = (n + m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n m)
    rwa [Nat.add_sub_cancel_left] at h
  have hCprod : Nat.choose (n + m) n
      = ∏ p ∈ Nat.primesLE (n + m), p ^ (Nat.choose (n + m) n).factorization p := by
    have h := Nat.prod_pow_factorization_choose (n + m) n (Nat.le_add_right n m)
    have hCsub : ∏ p ∈ Finset.range (n + m + 1),
          p ^ (Nat.choose (n + m) n).factorization p
        = ∏ p ∈ Nat.primesLE (n + m), p ^ (Nat.choose (n + m) n).factorization p := by
      apply (Finset.prod_subset _ _).symm
      · intro p hp
        simp only [Finset.mem_range]
        have hle := (Nat.mem_primesLE.mp hp).1
        omega
      · intro p hp hpn
        have hnp : ¬ Nat.Prime p := by
          intro hpr
          apply hpn
          rw [Nat.mem_primesLE]
          simp only [Finset.mem_range] at hp
          exact ⟨by omega, hpr⟩
        rw [Nat.factorization_eq_zero_of_not_prime _ hnp, pow_zero]
    rw [← hCsub]
    exact h.symm
  have hCsplit : Nat.choose (n + m) n
      = (∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p - n / p - m / p)) *
        (∏ p ∈ Nat.primesLE (n + m),
          p ^ ((Nat.choose (n + m) n).factorization p - ((n + m) / p - n / p - m / p))) := by
    conv_lhs => rw [hCprod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [← pow_add, Nat.add_sub_cancel'
      (legendre_le n m p (Nat.mem_primesLE.mp hp).2)]
  have hApos : ∀ K : ℕ, 0 < ∏ i ∈ Finset.Icc 1 K, i.totient := by
    intro K
    apply Finset.prod_pos
    intro i hi
    exact Nat.totient_pos.mpr (Finset.mem_Icc.mp hi).1
  have hPpos : ∀ p : ℕ, p ∈ Nat.primesLE (n + m) → 0 < p :=
    fun p hp => Nat.Prime.pos (Nat.mem_primesLE.mp hp).2
  have hQpos : ∀ p : ℕ, p ∈ Nat.primesLE (n + m) → 0 < p - 1 := by
    intro p hp
    have h2 : 2 ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    omega
  have keyNQ : ((∏ i ∈ Finset.Icc 1 (n + m), i.totient : ℕ) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p) : ℕ) : ℚ)
      = (((n + m).factorial : ℕ) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ ((n + m) / p) : ℕ) : ℚ) := by
    exact_mod_cast keyN
  have keynQ : ((∏ i ∈ Finset.Icc 1 n, i.totient : ℕ) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), p ^ (n / p) : ℕ) : ℚ)
      = (((n.factorial : ℕ)) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p) : ℕ) : ℚ) := by
    exact_mod_cast keyn
  have keymQ : ((∏ i ∈ Finset.Icc 1 m, i.totient : ℕ) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), p ^ (m / p) : ℕ) : ℚ)
      = (((m.factorial : ℕ)) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p) : ℕ) : ℚ) := by
    exact_mod_cast keym
  have hQsplitQ : ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ ((n + m) / p) : ℕ) : ℚ)
      = ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p) : ℕ) : ℚ)
        * (((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p) : ℕ) : ℚ)
          * ((∏ p ∈ Nat.primesLE (n + m),
            (p - 1) ^ ((n + m) / p - n / p - m / p) : ℕ) : ℚ)) := by
    exact_mod_cast hQsplit
  have hPsplitQ : ((∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p) : ℕ) : ℚ)
      = ((∏ p ∈ Nat.primesLE (n + m), p ^ (n / p) : ℕ) : ℚ)
        * (((∏ p ∈ Nat.primesLE (n + m), p ^ (m / p) : ℕ) : ℚ)
          * ((∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p - n / p - m / p) : ℕ) : ℚ)) := by
    exact_mod_cast hPsplit
  have hCeqQ : ((((Nat.choose (n + m) n : ℕ)) : ℚ) * (((n.factorial : ℕ)) : ℚ))
        * (((m.factorial : ℕ)) : ℚ) = (((n + m).factorial : ℕ) : ℚ) := by
    exact_mod_cast hCeq
  have hCsplitQ : (((Nat.choose (n + m) n : ℕ)) : ℚ)
      = ((∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p - n / p - m / p) : ℕ) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m),
          p ^ ((Nat.choose (n + m) n).factorization p - ((n + m) / p - n / p - m / p))
            : ℕ) : ℚ) := by
    exact_mod_cast hCsplit
  have hW : ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ ((n + m) / p - n / p - m / p)
        * p ^ (Nat.factorization (Nat.choose (n + m) n) p -
          ((n + m) / p - n / p - m / p)) : ℕ) : ℚ)
      = ((∏ p ∈ Nat.primesLE (n + m),
        (p - 1) ^ ((n + m) / p - n / p - m / p) : ℕ) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m),
          p ^ (Nat.factorization (Nat.choose (n + m) n) p -
            ((n + m) / p - n / p - m / p)) : ℕ) : ℚ) := by
    simp only [Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]
    rw [Finset.prod_mul_distrib]
  have hPn : ((∏ p ∈ Nat.primesLE (n + m), p ^ (n / p) : ℕ) : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply ne_of_gt
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hPpos p hp) _
  have hPm : ((∏ p ∈ Nat.primesLE (n + m), p ^ (m / p) : ℕ) : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply ne_of_gt
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hPpos p hp) _
  have hRp : ((∏ p ∈ Nat.primesLE (n + m), p ^ ((n + m) / p - n / p - m / p) : ℕ) : ℚ)
      ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply ne_of_gt
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hPpos p hp) _
  have hQn : ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p) : ℕ) : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply ne_of_gt
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hQpos p hp) _
  have hQm : ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p) : ℕ) : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply ne_of_gt
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hQpos p hp) _
  have hFn : (((n.factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hFm : (((m.factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have en : ((∏ i ∈ Finset.Icc 1 n, i.totient : ℕ) : ℚ)
      = (((n.factorial : ℕ)) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p) : ℕ) : ℚ)
        / (((∏ p ∈ Nat.primesLE (n + m), p ^ (n / p) : ℕ)) : ℚ) := by
    apply (eq_div_iff hPn).mpr
    exact keynQ
  have em : ((∏ i ∈ Finset.Icc 1 m, i.totient : ℕ) : ℚ)
      = (((m.factorial : ℕ)) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p) : ℕ) : ℚ)
        / (((∏ p ∈ Nat.primesLE (n + m), p ^ (m / p) : ℕ)) : ℚ) := by
    apply (eq_div_iff hPm).mpr
    exact keymQ
  rw [hQsplitQ, hPsplitQ, ← hCeqQ, hCsplitQ] at keyNQ
  have hcancel : ((∏ i ∈ Finset.Icc 1 (n + m), i.totient : ℕ) : ℚ)
        * (((∏ p ∈ Nat.primesLE (n + m), p ^ (n / p) : ℕ) : ℚ)
          * (((∏ p ∈ Nat.primesLE (n + m), p ^ (m / p) : ℕ) : ℚ)))
      = (((∏ p ∈ Nat.primesLE (n + m),
            (p - 1) ^ ((n + m) / p - n / p - m / p) : ℕ) : ℚ)
          * ((∏ p ∈ Nat.primesLE (n + m),
            p ^ (Nat.factorization (Nat.choose (n + m) n) p -
              ((n + m) / p - n / p - m / p)) : ℕ) : ℚ))
        * (((((n.factorial : ℕ)) : ℚ)
            * (((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (n / p) : ℕ) : ℚ)))
          * (((((m.factorial : ℕ)) : ℚ)
            * (((∏ p ∈ Nat.primesLE (n + m), (p - 1) ^ (m / p) : ℕ) : ℚ))))) := by
    apply mul_right_cancel₀ hRp
    have h := keyNQ
    ring_nf at h ⊢
    exact h
  have hmain : ((∏ i ∈ Finset.Icc 1 (n + m), i.totient : ℕ) : ℚ)
        / ((((∏ i ∈ Finset.Icc 1 n, i.totient : ℕ)) : ℚ)
          * ((((∏ i ∈ Finset.Icc 1 m, i.totient : ℕ))) : ℚ))
      = ((∏ p ∈ Nat.primesLE (n + m),
        (p - 1) ^ ((n + m) / p - n / p - m / p) : ℕ) : ℚ)
        * ((∏ p ∈ Nat.primesLE (n + m),
          p ^ (Nat.factorization (Nat.choose (n + m) n) p -
            ((n + m) / p - n / p - m / p)) : ℕ) : ℚ) := by
    rw [en, em]
    field_simp
    linear_combination hcancel
  refine ⟨∏ p ∈ Nat.primesLE (n + m),
    ((p - 1) ^ ((n + m) / p - n / p - m / p) *
      p ^ (Nat.factorization (Nat.choose (n + m) n) p -
        ((n + m) / p - n / p - m / p))), ?_, rfl⟩
  rw [htot, hW]
  exact hmain

end MetaMathlibExt
