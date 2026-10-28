/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.RoughNumbers
public import MathlibExt.NumberTheory.Sieve.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import MathlibExt.NumberTheory.Sieve.Rankin
import MathlibExt.NumberTheory.PrimeCounting.Mertens
import MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsup

/-!
# The sieve of Eratosthenes–Legendre

The number of `k`-rough integers `n ≤ N` (those with no prime factor `≤ k`) is given exactly by
Legendre's inclusion–exclusion formula `∑_{d ∣ k#} μ(d) ⌊N / d⌋`. Truncating the formula at
`d ≤ x` and bounding the remainder by Rankin's trick gives the asymptotic
`π(x, z) = x ∏_{p ≤ z} (1 - 1/p) + O(x log z · exp(-log x / log z))`, which is nontrivial as
long as `log z = o(log x / log log x)`. With Mertens' third theorem this yields
`π(x, (log x)^A) ~ e^{-γ} x / (A log log x)`.

## Main definitions

* `Nat.roughCount N k`: the number of `k`-rough integers in `[1, N]` (Legendre's function).

## Main statements

* `Nat.card_filter_coprime_eq_sum_moebius_mul_div`:
  `#{n ≤ N : (n, m) = 1} = ∑_{d ∣ m} μ(d) ⌊N/d⌋`.
* `Nat.roughCount_eq_sum_moebius_mul_div`: Legendre's identity for `roughCount`.
* `Nat.abs_roughCount_sub_mul_sum_moebius_div_le`: `π(x, z) = x ∑_{d ∣ P_z, d ≤ x} μ(d)/d +
  O(x log z · exp(-log x / log z))`.
* `Nat.abs_sum_moebius_div_sub_prod_le`: `∑_{d ∣ P_z, d ≤ x} μ(d)/d = ∏_{p ≤ z} (1 - 1/p) +
  O(log z · exp(-log x / log z))`.
* `Nat.abs_roughCount_sub_mul_prod_le`: `π(x, z) = x ∏_{p ≤ z} (1 - 1/p) +
  O(x log z · exp(-log x / log z))`.
* `Nat.roughCount_log_rpow_isEquivalent`: `π(x, (log x)^A) ~ e^{-γ} x / (A log log x)`.
* `Nat.card_filter_forall_not_dvd_isLittleO`: integers free of every prime of a set `P` with
  `∑_{p ∈ P} 1/p = ∞` have density zero.
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Nat

/-! ### Legendre's identity -/

private theorem sum_moebius_divisors_eq_ite (n : ℕ) :
    ∑ m ∈ n.divisors, (μ m : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) (coe_moebius_mul_coe_zeta (R := ℤ))
  simp only [coe_mul_zeta_apply, one_apply, intCoe_apply, Int.cast_id] at h
  exact h

/-- Legendre's identity: for `m ≠ 0`, the number of `n ∈ [1, N]` coprime to `m` is
`∑_{d ∣ m} μ(d) ⌊N / d⌋`. -/
theorem card_filter_coprime_eq_sum_moebius_mul_div {m : ℕ} (hm : m ≠ 0) (N : ℕ) :
    ((#{n ∈ Icc 1 N | n.Coprime m} : ℕ) : ℤ) = ∑ d ∈ m.divisors, μ d * ((N / d : ℕ) : ℤ) := by
  rw [show Icc 1 N = Ioc 0 N from rfl, Finset.card_filter, Nat.cast_sum]
  have h1 : ∀ n ∈ Ioc 0 N, ((if n.Coprime m then 1 else 0 : ℕ) : ℤ)
      = ∑ d ∈ m.divisors, if d ∣ n then μ d else 0 := by
    intro n _
    rw [← Finset.sum_filter]
    have : m.divisors.filter (fun d => d ∣ n) = (Nat.gcd n m).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, Nat.gcd_ne_zero_right h2⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hm⟩, h1⟩
    rw [this, sum_moebius_divisors_eq_ite]
    simp [Nat.Coprime]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div,
    mul_comm]

/-- `n` is `k`-rough iff it is positive and coprime to the primorial `k#`. -/
theorem isRough_iff_coprime_primorial {n k : ℕ} :
    n.IsRough k ↔ 0 < n ∧ n.Coprime (primorial k) := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨Nat.pos_of_ne_zero hn, Nat.coprime_of_dvd fun p hp hpn hpP => ?_⟩
    have := h p hp hpn
    have := hp.dvd_primorial_iff.mp hpP
    omega
  · rintro ⟨hn, hc⟩
    refine ⟨hn.ne', fun p hp hpn => ?_⟩
    by_contra hle
    have hpP : p ∣ primorial k := hp.dvd_primorial_iff.mpr (not_lt.mp hle)
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hpn hpP)

/-- Legendre's function `Φ(N, k)`: the number of `k`-rough integers in `[1, N]`, i.e. of
`1 ≤ n ≤ N` with no prime factor `≤ k`. With `N = ⌊x⌋` and `k = ⌊z⌋` this is the sifting
function `π(x, z)`. -/
def roughCount (N k : ℕ) : ℕ := #{n ∈ Icc 1 N | n.Coprime (primorial k)}

/-- `roughCount N k` counts the `k`-rough numbers `n ≤ N`. -/
theorem roughCount_eq_ncard (N k : ℕ) : roughCount N k = {n | n ≤ N ∧ n.IsRough k}.ncard := by
  rw [roughCount, ← Set.ncard_coe_finset]
  congr 1
  ext n
  simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq, isRough_iff_coprime_primorial]
  omega

/-- **Legendre's identity**: `Φ(N, k) = ∑_{d ∣ k#} μ(d) ⌊N / d⌋`. -/
theorem roughCount_eq_sum_moebius_mul_div (N k : ℕ) :
    (roughCount N k : ℤ) = ∑ d ∈ (primorial k).divisors, μ d * ((N / d : ℕ) : ℤ) :=
  card_filter_coprime_eq_sum_moebius_mul_div (primorial_pos k).ne' N

/-! ### Truncation and Rankin's trick -/

/-- `∑_{d ∣ n} d^{-s} = ∏_{p ∣ n} (1 + p^{-s})` for squarefree `n`. -/
private theorem sum_divisors_rpow_neg_eq_prod {n : ℕ} (hn : Squarefree n) (s : ℝ) :
    ∑ d ∈ n.divisors, (d : ℝ) ^ (-s) = ∏ p ∈ n.primeFactors, (1 + (p : ℝ) ^ (-s)) := by
  set g : ArithmeticFunction ℝ := prodPrimeFactors fun p => (p : ℝ) ^ (-s)
  have hg : ∀ d ∈ n.divisors, g d = (d : ℝ) ^ (-s) := by
    intro d hd
    have hdsq : Squarefree d := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [prodPrimeFactors_apply hdsq.ne_zero,
      Real.finsetProd_rpow _ _ (fun p _ => by positivity), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hdsq]
  have hgp : ∀ p ∈ n.primeFactors, g p = (p : ℝ) ^ (-s) := fun p hp => by
    rw [prodPrimeFactors_apply (prime_of_mem_primeFactors hp).ne_zero,
      (prime_of_mem_primeFactors hp).primeFactors, Finset.prod_singleton]
  rw [← Finset.sum_congr rfl hg,
    ← (IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_add_of_squarefree hn]
  exact Finset.prod_congr rfl fun p hp => by rw [hgp p hp]

/-- `∑_{d ∣ n} μ(d) / d = ∏_{p ∣ n} (1 - 1/p)` for squarefree `n`. -/
private theorem sum_divisors_moebius_div_eq_prod {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (μ d : ℝ) / d = ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  set g : ArithmeticFunction ℝ := prodPrimeFactors fun p => (p : ℝ)⁻¹
  have hg : ∀ d ∈ n.divisors, g d = (d : ℝ)⁻¹ := by
    intro d hd
    have hdsq : Squarefree d := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [prodPrimeFactors_apply hdsq.ne_zero, Finset.prod_inv_distrib, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hdsq]
  calc ∑ d ∈ n.divisors, (μ d : ℝ) / d = ∑ d ∈ n.divisors, (μ d : ℝ) * g d :=
        Finset.sum_congr rfl fun d hd => by rw [hg d hd, div_eq_mul_inv]
    _ = ∏ p ∈ n.primeFactors, (1 - g p) :=
        ((IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_sub_of_squarefree _ hn).symm
    _ = _ := Finset.prod_congr rfl fun p hp => by
        rw [prodPrimeFactors_apply (prime_of_mem_primeFactors hp).ne_zero,
          (prime_of_mem_primeFactors hp).primeFactors, Finset.prod_singleton]

/-- Truncated Legendre formula: uniformly for `x ≥ 1` and `z ≥ 3`,
`π(x, z) = x ∑_{d ∣ P_z, d ≤ x} μ(d) / d + O(x log z · exp(-log x / log z))`,
where `P_z = ⌊z⌋#` and `π(x, z) = Φ(⌊x⌋, ⌊z⌋)`. -/
theorem abs_roughCount_sub_mul_sum_moebius_div_le :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ z : ℝ, 3 ≤ z →
      |(roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) -
          x * ∑ d ∈ (primorial ⌊z⌋₊).divisors with ((d : ℕ) : ℝ) ≤ x, (μ d : ℝ) / d| ≤
        C * x * Real.log z * Real.exp (-(Real.log x / Real.log z)) := by
  obtain ⟨C, hC⟩ := card_smoothNumbersUpTo_le_mul_log_mul_exp
  refine ⟨C, fun x hx z hz => ?_⟩
  set S := (primorial ⌊z⌋₊).divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ x) with hS
  have hx0 : 0 ≤ x := by linarith
  have hid : (roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) =
      ∑ d ∈ S, (μ d : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ) := by
    have h1 := roughCount_eq_sum_moebius_mul_div ⌊x⌋₊ ⌊z⌋₊
    have h2 : (roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) =
        ∑ d ∈ (primorial ⌊z⌋₊).divisors, (μ d : ℝ) * (⌊x / (d : ℝ)⌋₊ : ℝ) := by
      have h3 := congrArg (fun t : ℤ => (t : ℝ)) h1
      simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at h3
      rw [h3]
      exact Finset.sum_congr rfl fun d _ => by rw [Nat.floor_div_natCast]
    rw [h2, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    split_ifs with h
    · rfl
    · have hd0 : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have : ⌊x / (d : ℝ)⌋₊ = 0 := by
        rw [Nat.floor_eq_zero, div_lt_one hd0]
        linarith [not_le.mp h]
      simp [this]
  have hdiff : (roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) - x * ∑ d ∈ S, (μ d : ℝ) / d =
      ∑ d ∈ S, (μ d : ℝ) * ((⌊x / (d : ℝ)⌋₊ : ℝ) - x / d) := by
    rw [hid, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hcard : (S.card : ℝ) ≤ ((Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊z⌋₊ + 1)).card : ℝ) := by
    have : S ⊆ Nat.smoothNumbersUpTo ⌊x⌋₊ (⌊z⌋₊ + 1) := by
      intro d hd
      rw [hS, Finset.mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers']
      refine ⟨Nat.le_floor hd.2, fun p hp hpd => ?_⟩
      have := (hp.dvd_primorial_iff).mp (dvd_trans hpd hd.1.1)
      omega
    exact_mod_cast Finset.card_le_card this
  have hbound : |∑ d ∈ S, (μ d : ℝ) * ((⌊x / (d : ℝ)⌋₊ : ℝ) - x / d)| ≤ S.card := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    have hm : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
    have hxd : 0 ≤ x / (d : ℝ) := by positivity
    have hfl : |(⌊x / (d : ℝ)⌋₊ : ℝ) - x / d| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [Nat.floor_le hxd, Nat.lt_floor_add_one (x / (d : ℝ))]
    rw [abs_mul, Nat.cast_one]
    nlinarith [abs_nonneg (μ d : ℝ), abs_nonneg ((⌊x / (d : ℝ)⌋₊ : ℝ) - x / d)]
  rw [hdiff]
  exact hbound.trans (hcard.trans (hC x hx z hz))

/-- The truncated Möbius sum over the divisors of `P_z = ⌊z⌋#` approximates the Mertens product:
uniformly for `x ≥ 1` and `z ≥ 3`,
`∑_{d ∣ P_z, d ≤ x} μ(d) / d = ∏_{p ≤ z} (1 - 1/p) + O(log z · exp(-log x / log z))`. -/
theorem abs_sum_moebius_div_sub_prod_le :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ z : ℝ, 3 ≤ z →
      |∑ d ∈ (primorial ⌊z⌋₊).divisors with ((d : ℕ) : ℝ) ≤ x, (μ d : ℝ) / d -
          ∏ p ∈ primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)| ≤
        C * Real.log z * Real.exp (-(Real.log x / Real.log z)) := by
  classical
  obtain ⟨C₁, hMert⟩ := sum_primesLE_inv_le_log_log_add
  set B := Real.log 4 + 6 with hB
  have hB0 : 0 ≤ B := by positivity
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  set E := Real.exp 1 with hE
  have hE0 : 0 < E := Real.exp_pos 1
  refine ⟨Real.exp (C₁ + E + E * B), ?_⟩
  intro x hx z hz
  have hlz : 1 < Real.log z := hlog3.trans_le (Real.log_le_log (by norm_num) hz)
  have hlz0 : 0 < Real.log z := by linarith
  set η := 1 / Real.log z with hη
  have hη0 : 0 < η := by positivity
  set δ := 1 - η with hδ
  have hx0 : 0 < x := by linarith
  set N := ⌊z⌋₊ with hN
  have hz1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hprime : ∀ p ∈ primesLE N, 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ z := by
    intro p hp
    have := Nat.mem_primesLE.mp hp
    exact ⟨by exact_mod_cast this.2.two_le,
      (Nat.cast_le.mpr this.1).trans (Nat.floor_le (by linarith))⟩
  have hneg : -δ = 1 / Real.log z - 1 := by rw [hδ, hη]; ring
  have hsum1 : ∑ p ∈ primesLE N, (p : ℝ) ^ (-δ) ≤
      ∑ p ∈ primesLE N, (p : ℝ)⁻¹ + E * η * ∑ p ∈ primesLE N, Real.log p / (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h2, hpz⟩ := hprime p hp
    rw [hneg]
    exact Real.rpow_inv_log_sub_one_le (by linarith) hpz hlz0
  have hmert : ∑ p ∈ primesLE N, (p : ℝ)⁻¹ ≤ Real.log (Real.log z) + C₁ := hMert z (by linarith)
  have hlp : E * η * ∑ p ∈ primesLE N, Real.log p / (p : ℝ) ≤ E + E * B := by
    have h := Chebyshev.sum_primesLE_log_div_le N hz1
    have hfl : Real.log N ≤ Real.log z :=
      Real.log_le_log (by exact_mod_cast hz1) (Nat.floor_le (by linarith))
    have : η * ∑ p ∈ primesLE N, Real.log p / (p : ℝ) ≤ 1 + B := by
      rw [hη, one_div_mul_eq_div, div_le_iff₀ hlz0]; nlinarith
    calc E * η * ∑ p ∈ primesLE N, Real.log p / (p : ℝ)
        = E * (η * ∑ p ∈ primesLE N, Real.log p / (p : ℝ)) := by ring
      _ ≤ E * (1 + B) := by gcongr
      _ = E + E * B := by ring
  have hsq := squarefree_primorial N
  have hpf := primeFactors_primorial N
  have hfull : ∑ d ∈ (primorial N).divisors, (μ d : ℝ) / d =
      ∏ p ∈ primesLE N, (1 - (p : ℝ)⁻¹) := by
    rw [sum_divisors_moebius_div_eq_prod hsq, hpf]
  have hdiv : ∑ d ∈ (primorial N).divisors, (d : ℝ) ^ (-δ) =
      ∏ p ∈ primesLE N, (1 + (p : ℝ) ^ (-δ)) := by
    rw [sum_divisors_rpow_neg_eq_prod hsq, hpf]
  have hprod : ∏ p ∈ primesLE N, (1 + (p : ℝ) ^ (-δ)) ≤
      Real.exp (∑ p ∈ primesLE N, (p : ℝ) ^ (-δ)) :=
    Real.prod_one_add_le_exp_sum _ fun p => by positivity
  have hexp : Real.exp (∑ p ∈ primesLE N, (p : ℝ) ^ (-δ)) ≤
      Real.log z * Real.exp (C₁ + E + E * B) := by
    calc _ ≤ Real.exp (Real.log (Real.log z) + (C₁ + E + E * B)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hlz0]
  have hxη : x ^ (-η) = Real.exp (-(Real.log x / Real.log z)) := by
    rw [Real.rpow_def_of_pos hx0, hη]
    congr 1
    ring
  -- Rankin on the tail
  have hterm : ∀ d ∈ (primorial N).divisors.filter (fun d => ¬ ((d : ℕ) : ℝ) ≤ x),
      |(μ d : ℝ) / d| ≤ x ^ (-η) * (d : ℝ) ^ (-δ) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have hxd : x < d := lt_of_not_ge hd.2
    have hd0 : (0 : ℝ) < d := by linarith
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    rw [abs_div, abs_of_pos hd0]
    have h1 : |(μ d : ℝ)| / d ≤ (d : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) hμ
    refine h1.trans ?_
    have hsplit : (d : ℝ) ^ (-δ) = (d : ℝ) ^ η * (d : ℝ)⁻¹ := by
      rw [hδ, show -(1 - η) = η + (-1) by ring, Real.rpow_add hd0, Real.rpow_neg_one]
    have hxd' : x ^ η ≤ (d : ℝ) ^ η := Real.rpow_le_rpow hx0.le hxd.le hη0.le
    have hxpos : 0 < x ^ η := by positivity
    have hx1 : x ^ (-η) * (d : ℝ) ^ η ≥ 1 := by
      rw [Real.rpow_neg hx0.le, ge_iff_le, ← div_eq_inv_mul, one_le_div hxpos]
      exact hxd'
    rw [hsplit, ← mul_assoc]
    have : 0 < (d : ℝ)⁻¹ := by positivity
    nlinarith
  have hsplit := Finset.sum_filter_add_sum_filter_not (primorial N).divisors
    (fun d => ((d : ℕ) : ℝ) ≤ x) (fun d => (μ d : ℝ) / d)
  rw [← hfull, ← hsplit]
  calc |∑ d ∈ (primorial N).divisors with ((d : ℕ) : ℝ) ≤ x, (μ d : ℝ) / d -
        (∑ d ∈ (primorial N).divisors with ((d : ℕ) : ℝ) ≤ x, (μ d : ℝ) / d +
          ∑ d ∈ (primorial N).divisors with ¬ ((d : ℕ) : ℝ) ≤ x, (μ d : ℝ) / d)|
      = |∑ d ∈ (primorial N).divisors with ¬ ((d : ℕ) : ℝ) ≤ x, (μ d : ℝ) / d| := by
        rw [sub_add_cancel_left, abs_neg]
    _ ≤ ∑ d ∈ (primorial N).divisors with ¬ ((d : ℕ) : ℝ) ≤ x, |(μ d : ℝ) / d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (primorial N).divisors with ¬ ((d : ℕ) : ℝ) ≤ x, x ^ (-η) * (d : ℝ) ^ (-δ) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ d ∈ (primorial N).divisors, x ^ (-η) * (d : ℝ) ^ (-δ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => by positivity)
    _ = x ^ (-η) * ∏ p ∈ primesLE N, (1 + (p : ℝ) ^ (-δ)) := by
        rw [← Finset.mul_sum, hdiv]
    _ ≤ x ^ (-η) * (Real.log z * Real.exp (C₁ + E + E * B)) := by
        gcongr
        exact hprod.trans hexp
    _ = _ := by rw [hxη]; ring

/-- **Legendre–Rankin**: uniformly for `x ≥ 1` and `z ≥ 3`,
`π(x, z) = x ∏_{p ≤ z} (1 - 1/p) + O(x log z · exp(-log x / log z))`. -/
theorem abs_roughCount_sub_mul_prod_le :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ z : ℝ, 3 ≤ z →
      |(roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) - x * ∏ p ∈ primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)| ≤
        C * x * Real.log z * Real.exp (-(Real.log x / Real.log z)) := by
  obtain ⟨C₁, h₁⟩ := abs_roughCount_sub_mul_sum_moebius_div_le
  obtain ⟨C₂, h₂⟩ := abs_sum_moebius_div_sub_prod_le
  refine ⟨C₁ + C₂, fun x hx z hz => ?_⟩
  have e1 := h₁ x hx z hz
  have e2 := h₂ x hx z hz
  set S := ∑ d ∈ (primorial ⌊z⌋₊).divisors with ((d : ℕ) : ℝ) ≤ x, (μ d : ℝ) / d
  have hx0 : 0 ≤ x := by linarith
  have hsplit : (roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) - x * ∏ p ∈ primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) =
      ((roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) - x * S) +
        x * (S - ∏ p ∈ primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hx0]
  nlinarith [mul_le_mul_of_nonneg_left e2 hx0]

/-! ### Sifting by `(log x)^A` -/

/-- For every `A > 0`, `π(x, (log x)^A) ~ e^{-γ} x / (A log log x)` as `x → ∞`. -/
theorem roughCount_log_rpow_isEquivalent {A : ℝ} (hA : 0 < A) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun x : ℝ => (roughCount ⌊x⌋₊ ⌊Real.log x ^ A⌋₊ : ℝ))
      (fun x : ℝ => x * Real.exp (-Real.eulerMascheroniConstant) /
        (A * Real.log (Real.log x))) := by
  obtain ⟨C, hC⟩ := abs_roughCount_sub_mul_prod_le
  set e := Real.exp (-Real.eulerMascheroniConstant) with he_def
  have he : 0 < e := Real.exp_pos _
  set V : ℝ → ℝ := fun z => ∏ p ∈ primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) with hV
  -- `z = (log x)^A → ∞`
  have hz : Filter.Tendsto (fun x : ℝ => Real.log x ^ A) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop
  have hL : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  -- Mertens' third theorem along `z`
  have hM : Filter.Tendsto (fun x : ℝ => V (Real.log x ^ A) * Real.log (Real.log x ^ A))
      Filter.atTop (nhds e) :=
    tendsto_prod_primesLE_one_sub_inv_mul_log.comp hz
  -- the error term is `O(1 / (log log x)^2)` relative to the main term
  have hsq : ∀ᶠ u : ℝ in Filter.atTop, Real.log u ^ 2 ≤ 1 / (4 * A) * u := by
    filter_upwards [(Real.isLittleO_pow_log_id_atTop (n := 2)).bound
      (show (0 : ℝ) < 1 / (4 * A) by positivity), Filter.eventually_ge_atTop 0] with u hu hu0
    simpa [Real.norm_eq_abs, abs_of_nonneg hu0, sq_abs] using hu
  have hErr : Filter.Tendsto (fun x : ℝ =>
      ((roughCount ⌊x⌋₊ ⌊Real.log x ^ A⌋₊ : ℝ) - x * V (Real.log x ^ A)) /
        (x * e / (A * Real.log (Real.log x)))) Filter.atTop (nhds 0) := by
    have hK : Filter.Tendsto (fun x : ℝ => |C| * A ^ 2 / e / Real.log (Real.log x) ^ 2)
        Filter.atTop (nhds 0) := by
      have := (Filter.tendsto_pow_atTop (two_ne_zero)).comp hL
      exact tendsto_const_nhds.div_atTop this
    refine squeeze_zero_norm' ?_ hK
    have hU : ∀ᶠ u : ℝ in Filter.atTop, 0 < u ∧ Real.log u ^ 2 ≤ 1 / (4 * A) * u ∧
        max 1 (Real.log 3 / A) ≤ Real.log u := by
      filter_upwards [hsq, Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop _),
        Filter.eventually_gt_atTop 0] with u h1 h2 h3
      exact ⟨h3, h1, h2⟩
    filter_upwards [Real.tendsto_log_atTop.eventually hU, Filter.eventually_ge_atTop 1]
      with x ⟨hu0, hsqx, hLx⟩ hx1
    set u := Real.log x with hu_def
    set L := Real.log u with hL_def
    have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hLx
    have hL3 : Real.log 3 / A ≤ L := le_trans (le_max_right _ _) hLx
    have hL0 : 0 < L := by linarith
    have hlogz : Real.log (u ^ A) = A * L := Real.log_rpow hu0 A
    have hAL : 0 < A * L := by positivity
    have hz3 : 3 ≤ u ^ A := by
      have : Real.log 3 ≤ Real.log (u ^ A) := by
        rw [hlogz]; rw [div_le_iff₀ hA] at hL3; linarith
      rwa [Real.log_le_log_iff (by norm_num) (by positivity)] at this
    have e1 := hC x hx1 (u ^ A) hz3
    rw [hlogz] at e1
    have hx0 : 0 < x := by linarith
    -- exponential decay `exp(-u / (A L)) ≤ L⁻⁴`
    have hE : Real.exp (-(u / (A * L))) ≤ 1 / L ^ 4 := by
      have hlogL : Real.log L ≤ L := by
        have := Real.log_le_sub_one_of_pos hL0; linarith
      have h4 : 4 * Real.log L ≤ u / (A * L) := by
        rw [le_div_iff₀ hAL]
        have : L ^ 2 * (4 * A) ≤ u := by
          have := mul_le_mul_of_nonneg_right hsqx (show (0:ℝ) ≤ 4 * A by positivity)
          field_simp at this; nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hlogL (show (0:ℝ) ≤ 4 * A * L by positivity)]
      calc Real.exp (-(u / (A * L))) ≤ Real.exp (-(4 * Real.log L)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = 1 / L ^ 4 := by
            rw [show -(4 * Real.log L) = Real.log (L ^ 4)⁻¹ by
              rw [Real.log_inv, Real.log_pow]; push_cast; ring]
            rw [Real.exp_log (by positivity), one_div]
    have hgpos : 0 < x * e / (A * L) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hgpos, div_le_iff₀ hgpos]
    calc |(roughCount ⌊x⌋₊ ⌊u ^ A⌋₊ : ℝ) - x * V (u ^ A)|
        ≤ C * x * (A * L) * Real.exp (-(u / (A * L))) := e1
      _ ≤ |C| * x * (A * L) * (1 / L ^ 4) := by
          gcongr
          exact le_abs_self _
      _ = |C| * A ^ 2 / e / L ^ 2 * (x * e / (A * L)) := by
          field_simp
  have hmain : Filter.Tendsto (fun x : ℝ => x * V (Real.log x ^ A) /
      (x * e / (A * Real.log (Real.log x)))) Filter.atTop (nhds 1) := by
    have h := hM.div_const e
    rw [div_self he.ne'] at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1,
      hL.eventually (Filter.eventually_gt_atTop 0)] with x hx hLx
    have hu0 : 0 < Real.log x := Real.log_pos hx
    rw [Real.log_rpow hu0]
    field_simp
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have := hmain.add hErr
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards with x
  simp only [Pi.div_apply]
  rw [← add_div, add_sub_cancel]

/-! ### Sifting by a set of primes with divergent reciprocal sum -/

open Classical in
/-- If `P` is a set of primes with `∑_{p ∈ P} 1/p = ∞`, then the integers `n ≤ x` divisible
by no prime of `P` have density zero: their number is `o(x)`. -/
theorem card_filter_forall_not_dvd_isLittleO (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdiv : ¬ Summable (P.indicator fun p : ℕ => (1 : ℝ) / p)) :
    (fun x : ℝ => ((#{n ∈ Icc 1 ⌊x⌋₊ | ∀ p ∈ P, ¬ p ∣ n} : ℕ) : ℝ))
      =o[Filter.atTop] (fun x => x) := by
  set f : ℕ → ℝ := P.indicator fun p : ℕ => (1 : ℝ) / p with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun _ _ => by positivity) n
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).1 hdiv
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := (htend.eventually_ge_atTop (Real.log (2 / ε))).exists
  set S := (Finset.range K).filter (· ∈ P) with hS
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => hP p (Finset.mem_filter.1 hp).2
  set M := ∏ p ∈ S, p with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 (fun p hp => (hSprime p hp).ne_zero)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
  have hpf : M.primeFactors = S := Nat.primeFactors_prod hSprime
  have hsumS : ∑ p ∈ S, (1 : ℝ) / p = ∑ i ∈ Finset.range K, f i := by
    rw [hS, Finset.sum_filter]
    rfl
  have hratio : (Nat.totient M : ℝ) ≤ (ε / 2) * M := by
    have h1 : (Nat.totient M : ℝ) = M * ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
      rw [← hpf]; exact cast_totient_eq_mul_prod_one_sub_inv M
    have h2 : ∏ p ∈ S, (1 - (p : ℝ)⁻¹) ≤ Real.exp (-∑ p ∈ S, (1 : ℝ) / p) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_le_prod₀
      · intro p hp
        have : (1 : ℝ) ≤ p := by exact_mod_cast (hSprime p hp).one_lt.le
        exact sub_nonneg.2 (inv_le_one_of_one_le₀ this)
      · intro p _
        simpa [one_div] using Real.one_sub_le_exp_neg ((p : ℝ)⁻¹)
    have h3 : Real.exp (-∑ p ∈ S, (1 : ℝ) / p) ≤ ε / 2 := by
      rw [hsumS]
      calc Real.exp (-∑ i ∈ Finset.range K, f i) ≤ Real.exp (-Real.log (2 / ε)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = ε / 2 := by
            rw [Real.exp_neg, Real.exp_log (by positivity)]
            field_simp
    rw [h1, mul_comm]
    exact mul_le_mul_of_nonneg_right (h2.trans h3) hMpos.le
  filter_upwards [Filter.eventually_ge_atTop (2 * M / ε), Filter.eventually_ge_atTop 0]
    with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hx0]
  set N := ⌊x⌋₊ with hN
  have hsub : (Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n) ⊆
      (Finset.Ico 1 (1 + N)).filter (fun n => M.Coprime n) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hn ⊢
    refine ⟨by omega, ?_⟩
    rw [hM, Nat.coprime_prod_left_iff]
    intro p hp
    exact (Nat.Prime.coprime_iff_not_dvd (hSprime p hp)).2
      (hn.2 p (Finset.mem_filter.1 hp).2)
  have hcard := (Finset.card_le_card hsub).trans (Nat.Ico_filter_coprime_le 1 N hM0)
  have hcardR : ((((Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card : ℕ) : ℝ) ≤
      (Nat.totient M : ℝ) * (((N / M : ℕ) : ℝ) + 1) := by exact_mod_cast hcard
  have hNM : ((N / M : ℕ) : ℝ) ≤ x / M :=
    (Nat.cast_div_le).trans (div_le_div_of_nonneg_right (Nat.floor_le hx0) hMpos.le)
  have htot0 : (0 : ℝ) ≤ Nat.totient M := Nat.cast_nonneg _
  have htotM : (Nat.totient M : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hMx : (M : ℝ) ≤ ε / 2 * x := by
    rw [div_le_iff₀ hε] at hx; linarith
  calc _ ≤ (Nat.totient M : ℝ) * (((N / M : ℕ) : ℝ) + 1) := hcardR
    _ ≤ (Nat.totient M : ℝ) * (x / M) + M := by nlinarith
    _ = (Nat.totient M : ℝ) / M * x + M := by ring
    _ ≤ ε / 2 * x + ε / 2 * x := by
        refine _root_.add_le_add (mul_le_mul_of_nonneg_right ?_ hx0) hMx
        rw [div_le_iff₀ hMpos]; linarith
    _ = ε * x := by ring

end Nat
