/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Squarefree

/-!
# Sizes of auxiliary primes in the generalized Carmichael number construction
-/

namespace MetaMathlibExt

open Finset Real

private theorem rpow_log_div_six_le_pow_floor {x : ℝ} (hx : 2 ≤ x) :
    (x / 6) ^ log x ≤ (x / 2) ^ ⌊log x⌋₊ := by
  have hx₀ : 0 < x := by linarith
  have hthree : x / 2 ≤ (3 : ℝ) ^ log x := calc
    x / 2 ≤ x := by linarith
    _ = (exp 1) ^ log x := by rw [← exp_mul, one_mul, exp_log hx₀]
    _ ≤ 3 ^ log x :=
      rpow_le_rpow (exp_pos _).le exp_one_lt_three.le (log_nonneg (by linarith))
  calc
    (x / 6) ^ log x = (x / 2) ^ log x / 3 ^ log x := by
      rw [← div_rpow (by positivity) (by norm_num)]
      congr 1
      ring
    _ ≤ (x / 2) ^ (log x - 1) := by
      rw [rpow_sub_one (by positivity)]
      gcongr
    _ ≤ (x / 2) ^ ⌊log x⌋₊ := by
      rw [← rpow_natCast]
      apply rpow_le_rpow_of_exponent_le (by linarith)
      linarith [Nat.lt_floor_add_one (log x)]

/-- **Size of the auxiliary primes in the construction.** For a natural number $z$, let $J$ be the
product of the primes $r$ with $z/2 \le r \le z$, and write $\omega(g)$ for the number of distinct
prime factors of $g$. For every real $A$ and all sufficiently large natural numbers $z$ the
following holds: if $j$, $g$ and $q$ are natural numbers with $1 \le j \le (\log z)^{2A}$,
$g \mid J$, $\omega(g) = \lfloor \log z \rfloor$, $q$ prime and $q = gj + 1$, then
$$(z/6)^{\log z} \le q \le 2 z^{\log z} (\log z)^{2A}.$$

In the paper the bound is stated for the primes $q$ of a chosen set $\mathcal{Q}_i$ of such primes
with a fixed $j = j_0$, and $A \ge 2$ is the constant of Conjecture 2; the statement here covers
every such $j$ and $q$, and every real $A$.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 3 (definitions of `J`, `𝓡_j`, `𝒬ᵢ`) and Lemma 1
(`integers-2026-A123-lem-1`). -/
public theorem rpow_log_le_prime_of_eq_mul_add_one_of_dvd_prod_primes
    (A : ℝ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ j g q : ℕ, 1 ≤ j → (j : ℝ) ≤ Real.log z ^ (2 * A) →
      g ∣ ∏ r ∈ (Finset.Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r →
      g.primeFactors.card = ⌊Real.log z⌋₊ → q.Prime → q = g * j + 1 →
        ((z : ℝ) / 6) ^ Real.log z ≤ q ∧
          (q : ℝ) ≤ 2 * (z : ℝ) ^ Real.log z * Real.log z ^ (2 * A) := by
  filter_upwards [Filter.eventually_ge_atTop 2] with z hz
  intro j g q hj hj' hdvd hcard hq heq
  let s := (Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r)
  have hs : ∀ r ∈ s, Nat.Prime r := fun _ hr => (mem_filter.mp hr).2.1
  have hsq : Squarefree (∏ r ∈ s, r) :=
    squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr =>
      Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs r hr)).mpr hpr))
      (fun r hr => (hs r hr).squarefree)
  have hsub : g.primeFactors ⊆ s := by
    rw [← Nat.primeFactors_prod hs]
    exact Nat.primeFactors_mono hdvd hsq.ne_zero
  have hprod : ∏ r ∈ g.primeFactors, (r : ℝ) = g := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hdvd)]
  have hz' : 2 ≤ (z : ℝ) := by exact_mod_cast hz
  have hlow : ((z : ℝ) / 2) ^ ⌊log z⌋₊ ≤ g := calc
    _ = ∏ _ ∈ g.primeFactors, ((z : ℝ) / 2) := by rw [prod_const, hcard]
    _ ≤ ∏ r ∈ g.primeFactors, (r : ℝ) :=
      prod_le_prod₀ (fun _ _ => by positivity) (fun _ hr => (mem_filter.mp (hsub hr)).2.2)
    _ = g := hprod
  have hupp : (g : ℝ) ≤ (z : ℝ) ^ log z := calc
    _ = ∏ r ∈ g.primeFactors, (r : ℝ) := hprod.symm
    _ ≤ ∏ _ ∈ g.primeFactors, (z : ℝ) := by
      apply prod_le_prod₀ (fun _ _ => by positivity)
      exact fun _ hr => Nat.cast_le.mpr (mem_Iic.mp (mem_filter.mp (hsub hr)).1)
    _ = (z : ℝ) ^ (⌊log z⌋₊ : ℝ) := by rw [prod_const, hcard, rpow_natCast]
    _ ≤ (z : ℝ) ^ log z :=
      rpow_le_rpow_of_exponent_le (by linarith) (Nat.floor_le (log_nonneg (by linarith)))
  constructor
  · refine (rpow_log_div_six_le_pow_floor hz').trans (hlow.trans ?_)
    rw [heq]
    exact_mod_cast (Nat.le_mul_of_pos_right g hj).trans (Nat.le_succ (g * j))
  · have hdouble : q ≤ 2 * (g * j) := by
      have := hq.two_le
      omega
    calc
      (q : ℝ) ≤ 2 * ((g : ℝ) * j) := by exact_mod_cast hdouble
      _ ≤ 2 * ((z : ℝ) ^ log z * log z ^ (2 * A)) := by gcongr
      _ = _ := (mul_assoc ..).symm

end MetaMathlibExt
