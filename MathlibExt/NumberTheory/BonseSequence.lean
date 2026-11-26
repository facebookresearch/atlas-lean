/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Bonse's inequality along subsequences of primes

We prove Diego Marques's sufficient condition for a sequence of prime indices to fail
Bonse's inequality infinitely often.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.BonseWanted

open Filter Topology

/-- **The $m$-th prime, counted from one.** For $m \ge 1$, $p_m$ is the $m$-th prime, so that
$p_1 = 2$, $p_2 = 3$, $p_3 = 5$; at $m = 0$ the value is also $2$. -/
noncomputable def primeNth (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- **Bonse sequence of prime indices.** For $m \ge 1$ let $p_m$ be the $m$-th prime, so that
$p_1 = 2$, and set $p_0 = 2$. A sequence $a_0, a_1, a_2, \ldots$ of natural numbers is a Bonse
sequence if $p_{a_n}^2 < p_{a_0} p_{a_1} \cdots p_{a_{n-1}}$ for all sufficiently large $n$.

In the paper's 1-based indexing the condition reads $p_{a_1} \cdots p_{a_n} > p_{a_{n+1}}^2$ for
all sufficiently large $n$. -/
def IsBonseSeq (a : ℕ → ℕ) : Prop :=
  ∀ᶠ n in atTop, (primeNth (a n) : ℝ) ^ 2 <
    ∏ k ∈ Finset.range n, (primeNth (a k) : ℝ)

private lemma primeNth_pos (m : ℕ) : 0 < primeNth m :=
  (Nat.prime_nth_prime (m - 1)).pos

-- Chebyshev's lower bound for π(p) first gives p ≤ 8 m log p. Bounding log p by
-- 2 √p and substituting the resulting bound on √p removes p from the right side.
private lemma primeNth_le_mul_log {m : ℕ} (hm : 1 ≤ m) :
    (primeNth m : ℝ) ≤ 16 * m * Real.log (16 * m) := by
  let p := primeNth m
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_nth_prime (m - 1)).two_le
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalf : 1 / 2 ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog : 1 / 2 ≤ Real.log p := hhalf.trans (Real.log_le_log (by norm_num) hp)
  have hbound : (p : ℝ) ≤ 8 * m * Real.log p := by
    by_cases h4 : 4 ≤ p
    · have hcount : Nat.primeCounting p = m := by
        change Nat.count Nat.Prime (Nat.nth Nat.Prime (m - 1) + 1) = m
        rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime]
        omega
      have h := Chebyshev.pi_ge_of_four_le h4
      rw [hcount, div_le_iff₀ (by linarith : 0 < Real.log p)] at h
      nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) by positivity) (sub_nonneg.mpr hhalf),
        mul_nonneg (show 0 ≤ (m : ℝ) by positivity) (show 0 ≤ Real.log p by linarith)]
    · have h3 : (p : ℝ) ≤ 3 := by exact_mod_cast (by omega : p ≤ 3)
      nlinarith [mul_nonneg (sub_nonneg.mpr hm') (show 0 ≤ Real.log p by linarith)]
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by positivity)
  have hlog_sqrt := Real.log_sqrt (show 0 ≤ (p : ℝ) by positivity)
  have hlog_le : Real.log p ≤ 2 * Real.sqrt p := by
    linarith [Real.log_le_self hs.le]
  have hs_le : Real.sqrt p ≤ 16 * m := by
    apply le_of_mul_le_mul_right (a := Real.sqrt p) _ hs
    nlinarith [Real.sq_sqrt (show 0 ≤ (p : ℝ) by positivity),
      mul_le_mul_of_nonneg_left hlog_le (show 0 ≤ 8 * (m : ℝ) by positivity)]
  have := Real.log_le_log hs hs_le
  change (p : ℝ) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left (show Real.log p ≤ 2 * Real.log (16 * m) by linarith)
    (show 0 ≤ 8 * (m : ℝ) by positivity)]

/-- **A sufficient condition for a non-Bonse sequence.** Let $a_0 < a_1 < a_2 < \cdots$ be a
strictly increasing sequence of positive integers and write $A_n = a_0 a_1 \cdots a_{n-1}$ for the
product of its first $n$ terms. Suppose that $(n + 1) \log \log a_n / \log a_{n+1} \to 0$ as
$n \to \infty$, and that there is a real number $c < 2$ such that $\log A_n / \log a_n < c$ for
infinitely many $n$. Then $a$ is not a Bonse sequence.

The second hypothesis is equivalent to $\liminf_n \log A_n / \log a_n < 2$. In the paper's
1-based indexing the hypotheses read $n \log \log a_n / \log a_{n+1} \to 0$ and
$\liminf \log A_n / \log a_{n+1} < 2$ with $A_n = a_1 \cdots a_n$.

Source: Diego Marques, "Bonse's Inequality along
Subsequences of Primes", Theorem 2. -/
theorem not_isBonseSeq_of_liminf_lt (a : ℕ → ℕ)
    (hmono : StrictMono a) (hpos : ∀ n, 1 ≤ a n)
    (hreg : Tendsto (fun n : ℕ =>
      ((n : ℝ) + 1) * Real.log (Real.log (a n)) /
        Real.log (a (n + 1))) atTop (𝓝 0))
    (hlim : ∃ c : ℝ, c < 2 ∧ ∃ᶠ n in atTop,
      Real.log (∏ k ∈ Finset.range n, (a k : ℝ)) /
        Real.log (a n) < c) :
    ¬ IsBonseSeq a := by
  obtain ⟨c, hc, hfreq⟩ := hlim
  intro hBonse
  have ha : Tendsto (fun n => (a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
  -- Work at n + 1, so a n is the largest index in the product.
  rw [← map_add_atTop_eq_nat 1] at hfreq
  change ∃ᶠ n in atTop, Real.log (∏ k ∈ Finset.range (n + 1), (a k : ℝ)) /
    Real.log (a (n + 1)) < c at hfreq
  have hB := (tendsto_add_atTop_nat 1).eventually hBonse
  obtain ⟨n, hratio, hsmall, hlarge, hbonse⟩ := (hfreq.and_eventually
    ((hreg.eventually_lt_const (show 0 < (2 - c) / 2 by linarith)).and
      (((Real.tendsto_log_atTop.comp ha).eventually_ge_atTop 32).and hB))).exists
  change 32 ≤ Real.log (a n) at hlarge
  have hm (k : ℕ) : 0 < (a k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (hpos k))
  have hp (k : ℕ) : 0 < (primeNth (a k) : ℝ) := by exact_mod_cast primeNth_pos _
  have han : 1 < a (n + 1) := (hpos n).trans_lt (hmono n.lt_succ_self)
  have hden : 0 < Real.log (a (n + 1)) := Real.log_pos (by exact_mod_cast han)
  have hfactor (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Real.log (primeNth (a k)) ≤ Real.log (a k) + 2 * Real.log (Real.log (a n)) := by
    have hle : Real.log (a k) ≤ Real.log (a n) :=
      Real.log_le_log (hm k) (by exact_mod_cast hmono.monotone (Finset.mem_range_succ_iff.mp hk))
    have hlogs : 16 * Real.log (16 * a k) ≤ Real.log (a n) ^ 2 := by
      rw [Real.log_mul (by norm_num) (hm k).ne']
      nlinarith [Real.log_le_self (show 0 ≤ (16 : ℝ) by norm_num),
        mul_nonneg (sub_nonneg.mpr hlarge) (show 0 ≤ Real.log (a n) by linarith)]
    have hle' : (primeNth (a k) : ℝ) ≤ a k * Real.log (a n) ^ 2 := by
      calc
        _ ≤ _ := primeNth_le_mul_log (hpos k)
        _ = a k * (16 * Real.log (16 * a k)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogs (hm k).le
    have := Real.log_le_log (hp k) hle'
    rwa [Real.log_mul (hm k).ne' (pow_ne_zero 2 (by linarith)), Real.log_pow,
      Nat.cast_ofNat] at this
  have hsum := Finset.sum_le_sum hfactor
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [Real.log_prod (fun k _ => (hm k).ne'), div_lt_iff₀ hden] at hratio
  change ((n : ℝ) + 1) * Real.log (Real.log (a n)) / Real.log (a (n + 1)) < _ at hsmall
  rw [div_lt_iff₀ hden] at hsmall
  have hlogB := Real.log_lt_log (pow_pos (hp (n + 1)) 2) hbonse
  rw [Real.log_pow, Real.log_prod (fun k _ => (hp k).ne')] at hlogB
  have hindex : a (n + 1) ≤ primeNth (a (n + 1)) := by
    have := Nat.add_two_le_nth_prime (a (n + 1) - 1)
    unfold primeNth
    omega
  have hlog_index := Real.log_le_log (hm (n + 1)) (Nat.cast_le (α := ℝ).mpr hindex)
  push_cast at hsum hlogB
  linarith

/-- **A sufficient condition for a Bonse sequence.** Let $a_0 < a_1 < a_2 < \cdots$ be a strictly
increasing sequence of positive integers and write $A_n = a_0 a_1 \cdots a_{n-1}$ for the product
of its first $n$ terms. If there is a real number $c > 2$ such that $\log A_n / \log a_n > c$ for
all sufficiently large $n$, then $a$ is a Bonse sequence.

The hypothesis is equivalent to $\liminf_n \log A_n / \log a_n > 2$, an infinite limit inferior
included. In the paper's 1-based indexing it reads $\liminf \log A_n / \log a_{n+1} > 2$ with
$A_n = a_1 \cdots a_n$.

Source: Diego Marques, "Bonse's Inequality along
Subsequences of Primes", Theorem 1. -/
theorem isBonseSeq_of_liminf_gt (a : ℕ → ℕ)
    (hmono : StrictMono a) (hpos : ∀ n, 1 ≤ a n)
    (hlim : ∃ c : ℝ, 2 < c ∧ ∀ᶠ n in atTop,
      c < Real.log (∏ k ∈ Finset.range n, (a k : ℝ)) /
        Real.log (a n)) :
    IsBonseSeq a := by
  obtain ⟨c, hc, hratio⟩ := hlim
  have ha : Tendsto (fun n => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop)
  have hsmall := ha.eventually (Real.isLittleO_log_id_atTop.bound
    (show 0 < (c - 2) / 4 by linarith))
  filter_upwards [hratio, ha.eventually_ge_atTop 32, hsmall] with n hratio hlarge hsmall
  have ha_pos (k : ℕ) : 0 < (a k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (hpos k))
  have hp_pos (k : ℕ) : 0 < (primeNth (a k) : ℝ) := by exact_mod_cast primeNth_pos _
  have hlog : 0 < Real.log (a n) := by linarith
  have hratio' := (lt_div_iff₀ hlog).mp hratio
  -- Chebyshev's bound gives p_m ≤ m (log m)^2 once log m is large enough.
  have hlogs : 16 * Real.log (16 * a n) ≤ Real.log (a n) ^ 2 := by
    rw [Real.log_mul (by norm_num) (ha_pos n).ne']
    nlinarith [Real.log_le_self (show 0 ≤ (16 : ℝ) by norm_num),
      mul_nonneg (sub_nonneg.mpr hlarge) hlog.le]
  have hprime : (primeNth (a n) : ℝ) ≤ a n * Real.log (a n) ^ 2 := by
    calc
      _ ≤ 16 * a n * Real.log (16 * a n) := primeNth_le_mul_log (hpos n)
      _ = a n * (16 * Real.log (16 * a n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogs (ha_pos n).le
  have hlog_prime := Real.log_le_log (hp_pos n) hprime
  rw [Real.log_mul (ha_pos n).ne' (pow_ne_zero 2 hlog.ne'), Real.log_pow,
    Nat.cast_ofNat] at hlog_prime
  -- The log-log correction fits inside the strict margin c - 2.
  change ‖Real.log (Real.log (a n))‖ ≤ (c - 2) / 4 * ‖Real.log (a n)‖ at hsmall
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog] at hsmall
  have herr := (le_abs_self _).trans hsmall
  have hprod : (∏ k ∈ Finset.range n, (a k : ℝ)) ≤
      ∏ k ∈ Finset.range n, (primeNth (a k) : ℝ) := by
    refine Finset.prod_le_prod₀ (fun k _ => (ha_pos k).le) fun k _ => ?_
    have hindex : a k ≤ primeNth (a k) := by
      have := Nat.add_two_le_nth_prime (a k - 1)
      unfold primeNth
      omega
    exact_mod_cast hindex
  have hlog_prod := Real.log_le_log (Finset.prod_pos fun k _ => ha_pos k) hprod
  apply (Real.log_lt_log_iff (pow_pos (hp_pos n) 2)
    (Finset.prod_pos fun k _ => hp_pos k)).mp
  rw [Real.log_pow, Nat.cast_ofNat]
  nlinarith only [hlog_prime, herr, hratio', hlog_prod]

end MathlibExt.NumberTheory.BonseWanted
