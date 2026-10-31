/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.PrimeCounting

/-!
# Mertens' first and second theorems

This file proves Mertens' first theorem for the von Mangoldt function,
`∑_{n ≤ x} Λ(n) / n = log x + O(1)`, with an explicit constant. The proof compares
Legendre's identity `log N! = ∑_{d ≤ N} Λ(d) ⌊N / d⌋` with Stirling's lower bound for
`log N!` and Chebyshev's upper bound `ψ(x) ≤ (log 4 + 4) x`.

It then deduces Mertens' second theorem `∑_{p ≤ x} 1 / p = log log x + O(1)` by Abel summation,
first for `∑_{n ≤ x} Λ(n) / (n log n)` and then removing the prime powers. Mertens' third
theorem is in `MathlibExt.NumberTheory.PrimeCounting.MertensThird`.

## Main statements

* `Chebyshev.log_factorial_eq_sum_vonMangoldt_mul_div`: Legendre's identity in von Mangoldt
  form.
* `Chebyshev.abs_sum_vonMangoldt_div_sub_log_le`: Mertens' first theorem with the explicit
  constant `log 4 + 6`.
* `Chebyshev.sum_vonMangoldt_div_sub_log_isBigO_one`: the same statement as a `IsBigO` bound.
* `Chebyshev.sum_primesLE_log_div_le`: the upper bound `∑_{p ≤ N} log p / p ≤ log N + O(1)`.
* `Chebyshev.abs_sum_primesLE_inv_sub_log_log_le`: Mertens' second theorem,
  `|∑_{p ≤ x} 1 / p - log log x| ≤ C` for `x ≥ 2`.
-/

@[expose] public section

open Finset ArithmeticFunction

namespace Chebyshev

/-- Legendre's identity in von Mangoldt form: `log N! = ∑_{d ≤ N} Λ(d) ⌊N / d⌋`. -/
theorem log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  have hcast : ((N.factorial : ℕ) : ℝ) = ∏ m ∈ Finset.Ico 1 (N + 1), (m : ℝ) := by
    have h := Finset.prod_Ico_id_eq_factorial N
    rw [← h, Finset.prod_natCast]
  rw [hcast, Real.log_prod (fun m hm => by
    rw [Finset.mem_Ico] at hm
    exact_mod_cast ne_of_gt hm.1)]
  have h1 : ∀ m ∈ Finset.Ico 1 (N + 1), Real.log (m : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then vonMangoldt d else 0) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmpos : 0 < m := hm.1
    have hmN : m ≤ N := by omega
    have hsub : m.divisors ⊆ Finset.Icc 1 N := by
      intro x hx
      rw [Nat.mem_divisors] at hx
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hx.1 hmpos, le_trans (Nat.le_of_dvd hmpos hx.1) hmN⟩
    have hfilter : m.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ m) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨hsub (Nat.mem_divisors.mpr ⟨hdvd, ne_of_gt hmpos⟩), hdvd⟩
      · rintro ⟨-, hdvd⟩
        exact ⟨hdvd, ne_of_gt hmpos⟩
    conv_lhs => rw [← vonMangoldt_sum (n := m), hfilter, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  have hcard : ({m ∈ Finset.Ico 1 (N + 1) | d ∣ m}.card : ℝ)
      = ((N / d : ℕ) : ℝ) := by
    congr 1
    have hset : {m ∈ Finset.Ico 1 (N + 1) | d ∣ m} = {x ∈ Finset.Ioc 0 N | d ∣ x} := by
      ext x
      simp [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  simp [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

/-- **Mertens' first theorem**, with an explicit constant:
`|∑_{n ≤ x} Λ(n) / n - log x| ≤ log 4 + 6` for every `x ≥ 1`. -/
theorem abs_sum_vonMangoldt_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt n / (n : ℝ) - Real.log x|
      ≤ Real.log 4 + 6 := by
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hNge1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN1 : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
  set A := ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d / (d : ℝ) with hAdef
  have hpsi : ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d = Chebyshev.psi (N:ℝ) := by
    have h := Chebyshev.psi_eq_sum_Icc (N:ℝ)
    rw [Nat.floor_natCast] at h
    have hsplit : Finset.Icc 0 N = insert 0 (Finset.Ioc 0 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)] at h
    simp at h
    exact h.symm
  have hNA : Real.log (N.factorial : ℝ) ≤ (N:ℝ) * A := by
    rw [log_factorial_eq_sum_vonMangoldt_mul_div, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hle : ((N / d : ℕ):ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
    have hnn : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    calc vonMangoldt d * ((N/d:ℕ):ℝ)
        ≤ vonMangoldt d * ((N:ℝ)/(d:ℝ)) :=
          mul_le_mul_of_nonneg_left hle hnn
      _ = (N:ℝ) * (vonMangoldt d / (d:ℝ)) := by ring
  have hStirl := Stirling.le_log_factorial_stirling (n := N) (by omega)
  have hlogNnn : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNge1R
  have h2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Real.log_nonneg
    have hpi := Real.two_le_pi
    linarith
  have hlow : (N:ℝ) * Real.log (N:ℝ) - (N:ℝ) ≤ Real.log (N.factorial : ℝ) := by
    linarith
  have hdiff : ∀ d ∈ Finset.Ioc 0 N, (N:ℝ)/(d:ℝ) - ((N/d:ℕ):ℝ) ≤ 1 := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hdposN : 0 < d := by omega
    have hmod : N % d < d := Nat.mod_lt N hdposN
    have hdecomp : d * (N / d) + N % d = N := Nat.div_add_mod N d
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdposN
    have heq : (N:ℝ)/(d:ℝ) - ((N/d:ℕ):ℝ) = ((N % d : ℕ):ℝ)/(d:ℝ) := by
      have hcast : ((d * (N/d) + N % d : ℕ):ℝ) = (N:ℝ) := by rw [hdecomp]
      push_cast at hcast
      field_simp
      linarith
    rw [heq, div_le_one hdR]
    exact_mod_cast le_of_lt hmod
  have hup : (N:ℝ) * A ≤ Real.log (N.factorial : ℝ) + Chebyshev.psi (N:ℝ) := by
    rw [log_factorial_eq_sum_vonMangoldt_mul_div, Finset.mul_sum, ← hpsi,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have hnn : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    have h1 := hdiff d hd
    have e1 : (N:ℝ) * (vonMangoldt d / (d:ℝ))
        = vonMangoldt d * ((N:ℝ)/(d:ℝ)) := by ring
    rw [e1]
    have hmul := mul_le_mul_of_nonneg_left h1 hnn
    rw [mul_one] at hmul
    have hsub := mul_sub (vonMangoldt d) ((N:ℝ)/(d:ℝ)) ((N/d:ℕ):ℝ)
    linarith
  have hfact : Real.log (N.factorial : ℝ) ≤ (N:ℝ) * Real.log (N:ℝ) := by
    have h := Nat.factorial_le_pow N
    have hpos : (0:ℝ) < (N.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos N
    have hle : ((N.factorial : ℕ):ℝ) ≤ ((N ^ N : ℕ):ℝ) := by exact_mod_cast h
    rw [Nat.cast_pow] at hle
    calc Real.log (N.factorial:ℝ) ≤ Real.log ((N:ℝ)^N) :=
          Real.log_le_log hpos hle
      _ = (N:ℝ) * Real.log (N:ℝ) := by rw [Real.log_pow]
  have hpsile := Chebyshev.psi_le_const_mul_self (x := (N:ℝ)) (le_of_lt hNpos)
  have hAge1 : Real.log (N:ℝ) - 1 ≤ A := by
    have hmul : (N:ℝ) * (Real.log (N:ℝ) - 1) ≤ (N:ℝ) * A := by
      have hexpand : (N:ℝ)*(Real.log (N:ℝ) - 1)
        = (N:ℝ)*Real.log (N:ℝ) - (N:ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_left hmul hNpos
  have hAle1 : A ≤ Real.log (N:ℝ) + Real.log 4 + 4 := by
    have hmul : (N:ℝ) * A ≤ (N:ℝ) * (Real.log (N:ℝ) + Real.log 4 + 4) := by
      have hexpand : (N:ℝ)*(Real.log (N:ℝ) + Real.log 4 + 4)
        = (N:ℝ)*Real.log (N:ℝ) + (Real.log 4 + 4)*(N:ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_left hmul hNpos
  have hlogNx : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log hNpos hNx
  have hx2N : x ≤ 2 * (N:ℝ) := by linarith
  have hlogx : Real.log x ≤ Real.log (N:ℝ) + Real.log 2 := by
    have h2N : Real.log x ≤ Real.log (2 * (N:ℝ)) :=
      Real.log_le_log (by linarith) hx2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h2N
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : A - Real.log x ≤ Real.log 4 + 4 := by linarith
  have h2 : -(Real.log 4 + 6) ≤ A - Real.log x := by linarith
  rw [abs_le]
  constructor <;> linarith


/-- **Mertens' first theorem**: `∑_{n ≤ x} Λ(n) / n = log x + O(1)` as `x → ∞`. -/
theorem sum_vonMangoldt_div_sub_log_isBigO_one :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt n / (n : ℝ) - Real.log x)
      =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4 + 6) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simpa using abs_sum_vonMangoldt_div_sub_log_le x hx

/-- The prime part of Mertens' first theorem, as an upper bound:
`∑_{p ≤ N} log p / p ≤ log N + log 4 + 6` for every `N`. -/
theorem sum_primesLE_log_div_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) ≤ Real.log N + (Real.log 4 + 6) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    positivity
  have h := abs_sum_vonMangoldt_div_sub_log_le (N : ℝ) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at h
  have hle : ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 N, vonMangoldt n / (n : ℝ) := by
    calc ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ)
        = ∑ p ∈ Nat.primesLE N, vonMangoldt p / (p : ℝ) :=
          Finset.sum_congr rfl fun p hp => by
            rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
            fun n _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
          have := Nat.mem_primesLE.mp hp
          exact Finset.mem_Ioc.mpr ⟨this.2.pos, this.1⟩
  linarith [(abs_le.mp h).2]

section MertensSecond

open MeasureTheory Set intervalIntegral

-- N3(a): ∫ 1/(t log t) = log log x - log log 2
private theorem integral_inv_mul_log_facts_a (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioc 2 x, 1 / (t * Real.log t)
      = Real.log (Real.log x) - Real.log (Real.log 2) := by
  rw [← intervalIntegral.integral_of_le hx]
  have hderiv : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun t => Real.log (Real.log t)) (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt htpos)
    have h3 := h1.log (ne_of_gt hlogpos)
    have heq : t⁻¹ / Real.log t = 1 / (t * Real.log t) := by field_simp
    rwa [heq] at h3
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t)) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    apply ContinuousOn.div continuousOn_const _ (fun t ht => by
      rw [Set.mem_Icc] at ht
      have h1 : (0:ℝ) < t := by linarith
      have h2 : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
      exact ne_of_gt (by positivity))
    exact continuousOn_id.mul (ContinuousOn.log continuousOn_id (fun t ht => by
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (by linarith : (0:ℝ) < t)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

-- Node proofs (n3b).
open MeasureTheory Set intervalIntegral

-- N3(b): ∫ 1/(t log²t) = 1/log 2 - 1/log x
private theorem integral_inv_mul_log_sq_facts_b (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioc 2 x, 1 / (t * Real.log t ^ 2)
      = 1 / Real.log 2 - 1 / Real.log x := by
  rw [← intervalIntegral.integral_of_le hx]
  have hderiv : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun t => -(Real.log t)⁻¹) (1 / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt htpos)
    have h2 := h1.inv (ne_of_gt hlogpos)
    have h3 := h2.neg
    have heq : -(-t⁻¹ / Real.log t ^ 2) = 1 / (t * Real.log t ^ 2) := by field_simp
    rwa [heq] at h3
  have hlog : ContinuousOn (fun t : ℝ => Real.log t ^ 2) (Set.Icc 2 x) := by
    apply ContinuousOn.pow
    apply ContinuousOn.log continuousOn_id (fun t ht => by
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (by linarith : (0:ℝ) < t))
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t ^ 2)) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    apply ContinuousOn.div continuousOn_const _ (fun t ht => by
      rw [Set.mem_Icc] at ht
      have h1 : (0:ℝ) < t := by linarith
      have h2 : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
      exact ne_of_gt (by positivity))
    exact continuousOn_id.mul hlog
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [one_div, one_div]
  ring

-- Node proofs (n5).
private theorem geom_prime_pow_le (p N : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ Finset.Icc 2 N, ((1 : ℝ) / p) ^ k ≤ 2 / (p : ℝ) ^ 2 := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hx0 : (0:ℝ) ≤ 1 / p := by positivity
  have hx1 : (1:ℝ) / p < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < p)]
    linarith
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 2) (n := N + 1) (x := (1:ℝ)/p) hx0 hx1
  rw [Finset.Ico_add_one_right_eq_Icc] at hgeom
  have key : ((1:ℝ)/p)^2 / (1 - 1/p) = 1 / ((p:ℝ) * (p - 1)) := by
    field_simp
  have hfin : (1:ℝ) / ((p:ℝ) * (p - 1)) ≤ 2 / (p:ℝ)^2 := by
    have hA : (0:ℝ) < (p:ℝ) * (p - 1) := mul_pos hp0 (by linarith)
    have hB : (0:ℝ) < (p:ℝ)^2 := by positivity
    rw [le_div_iff₀ hB]
    have e : (1:ℝ) / ((p:ℝ) * (p - 1)) * (p:ℝ)^2
        = (p:ℝ)^2 / ((p:ℝ) * (p - 1)) := by ring
    rw [e, div_le_iff₀ hA]
    nlinarith [mul_nonneg (le_of_lt hp0) (show (0:ℝ) ≤ p - 2 by linarith)]
  rw [key] at hgeom
  exact le_trans hgeom hfin

private theorem nonprime_primePow_eq_prime_pow (N : ℕ) (n : ℕ)
    (hn : n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)) :
    ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ k ≤ N ∧ p ≤ N ∧ p ^ k = n := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨h1, h2⟩, hpp, hnp⟩ := hn
  obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff n |>.mp hpp
  have hk1 : k ≠ 1 := by
    rintro rfl
    simp only [pow_one] at hnp
    exact hnp hp
  have hk2 : 2 ≤ k := by omega
  have hpN : p ≤ N := by
    calc p ≤ p ^ k := Nat.le_self_pow (by omega) p
      _ ≤ N := h2
  have hkN : k ≤ N := by
    apply le_of_lt
    calc k < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ p ^ k := Nat.pow_le_pow_left (Nat.Prime.two_le hp) k
      _ ≤ N := h2
  exact ⟨p, k, hp, hk2, hkN, hpN, rfl⟩

-- N5: sum of 1/n over non-prime prime powers ≤ 2
private theorem sum_inv_nonprime_primePow_le_two (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (1 : ℝ) / n ≤ 2 := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hempty : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, -, -⟩ := hn
      omega
    rw [hempty, Finset.sum_empty]
    norm_num
  · set T : Finset (ℕ × ℕ) :=
      ((Finset.Icc 2 N) ×ˢ (Finset.Icc 2 N)).filter
        (fun q => q.1.Prime ∧ q.1 ^ q.2 ≤ N) with hTdef
    set φ : ℕ × ℕ → ℕ := fun q => q.1 ^ q.2 with hφdef
    have hinj : ∀ a ∈ T, ∀ b ∈ T, φ a = φ b → a = b := by
      intro a ha b hb hab
      rw [hTdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at ha hb
      simp only [hφdef] at hab
      obtain ⟨⟨⟨ha1, -⟩, ⟨ha2, -⟩⟩, haP, -⟩ := ha
      obtain ⟨⟨⟨hb1, -⟩, ⟨hb2, -⟩⟩, hbP, -⟩ := hb
      have h := Nat.Prime.pow_inj' haP hbP (by omega) (by omega) hab
      obtain ⟨h1, h2⟩ := h
      exact Prod.ext h1 h2
    have hmem : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        ∃ q ∈ T, φ q = n := by
      intro n hn
      obtain ⟨p, k, hp, hk2, hkN, hpN, rfl⟩ := nonprime_primePow_eq_prime_pow N n hn
      have hPk : p ^ k ≤ N :=
        (Finset.mem_Icc.mp (Finset.mem_of_mem_filter _ hn)).2
      refine ⟨(p, k), ?_, rfl⟩
      rw [hTdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      change ((2 ≤ p ∧ p ≤ N) ∧ 2 ≤ k ∧ k ≤ N) ∧ p.Prime ∧ p ^ k ≤ N
      exact ⟨⟨⟨hp.two_le, hpN⟩, ⟨hk2, hkN⟩⟩, hp, hPk⟩
    have h1 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (1:ℝ)/n
        ≤ ∑ q ∈ T, (1:ℝ)/(φ q) := by
      have hsub : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
          ⊆ T.image φ := by
        intro n hn
        obtain ⟨q, hqT, rfl⟩ := hmem n hn
        exact Finset.mem_image_of_mem φ hqT
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by positivity : ∀ n ∈ T.image φ, n ∉ _ → (0:ℝ) ≤ 1/(n:ℝ))
      have heq : ∑ x ∈ T.image φ, (1:ℝ)/(x:ℝ) = ∑ q ∈ T, (1:ℝ)/((φ q : ℕ):ℝ) :=
        Finset.sum_image (fun a _ b _ hab => hinj a ‹_› b ‹_› hab)
      rw [heq] at hle
      exact hle
    have h2 : ∑ q ∈ T, (1:ℝ)/(φ q)
        ≤ ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, ((1:ℝ)/p)^k := by
      have hsub2 : T ⊆ (Finset.Icc 2 N) ×ˢ (Finset.Icc 2 N) := by
        rw [hTdef]
        exact Finset.filter_subset _ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub2
        (fun q _ _ => by positivity :
          ∀ q ∈ (Finset.Icc 2 N ×ˢ Finset.Icc 2 N), q ∉ T → (0:ℝ) ≤ 1 / (φ q))
      have heq : ∑ q ∈ (Finset.Icc 2 N ×ˢ Finset.Icc 2 N), (1:ℝ)/(φ q)
          = ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, ((1:ℝ)/p)^k := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hp
        have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le (by norm_num) hp.1)
        simp only [hφdef]
        rw [Nat.cast_pow, div_pow, one_pow]
      exact le_trans hle (le_of_eq heq)
    have h3 : ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, ((1:ℝ)/p)^k
        ≤ ∑ p ∈ Finset.Icc 2 N, 2/(p:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.mem_Icc] at hp
      exact geom_prime_pow_le p N hp.1
    have h4 : ∑ p ∈ Finset.Icc 2 N, (2:ℝ)/(p:ℝ)^2 ≤ 2 := by
      have hIcc : Finset.Icc 2 N = Finset.Ioc 1 N := by
        ext x
        simp [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hIcc]
      have hsq := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := N) (by norm_num) hN
      simp only [Nat.cast_one, inv_one] at hsq
      calc ∑ p ∈ Finset.Ioc 1 N, 2/(p:ℝ)^2
          = 2 * ∑ i ∈ Finset.Ioc 1 N, ((i:ℝ)^2)⁻¹ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
        _ ≤ 2 * (1 - (N:ℝ)⁻¹) := by
            apply mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ ≤ 2 := by
            have hpos : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
            linarith
    exact le_trans (le_trans (le_trans h1 h2) h3) h4

-- N4: Mertens II, Lambda form (Abel summation).
private theorem abs_sum_vonMangoldt_div_mul_log_sub_loglog_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ))
        - Real.log (Real.log x)| ≤ C := by
  use 1 + 2 * (Real.log 4 + 6) / Real.log 2 + |Real.log (Real.log 2)|
  intro x hx
  have hx1 : 1 ≤ x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have hCnn : (0:ℝ) ≤ Real.log 4 + 6 := by
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hSeq : ∀ t : ℝ, 1 ≤ t →
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ))
        = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, vonMangoldt k / (k:ℝ) := by
    intro t ht
    have hM : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
    have hsplit : Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp
  have hRbound : ∀ t : ℝ, 1 ≤ t →
      |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t|
        ≤ Real.log 4 + 6 := by
    intro t ht
    rw [hSeq t ht]
    exact Chebyshev.abs_sum_vonMangoldt_div_sub_log_le t ht
  have hc0 : (fun k : ℕ => vonMangoldt k / (k:ℝ)) 0 = 0 := by simp
  have hc1 : (fun k : ℕ => vonMangoldt k / (k:ℝ)) 1 = 0 := by
    simp [vonMangoldt_apply_one]
  have hdiff : ∀ t ∈ Set.Icc (2:ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => (Real.log t)⁻¹) t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have htpos : (0:ℝ) < t := by linarith
    have hlog : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < t))
    exact (Real.differentiableAt_log (ne_of_gt htpos)).inv hlog
  have hnum : ContinuousOn (fun t : ℝ => -t⁻¹) (Set.Icc 2 x) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [Set.mem_Icc] at ht
    exact ne_of_gt (by linarith : (0:ℝ) < t)
  have hden : ContinuousOn (fun t : ℝ => Real.log t ^ 2) (Set.Icc 2 x) := by
    apply ContinuousOn.pow
    exact ContinuousOn.log continuousOn_id (fun t ht => by
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (by linarith : (0:ℝ) < t))
  have hfrac : ContinuousOn (fun t : ℝ => -t⁻¹ / Real.log t ^ 2) (Set.Icc 2 x) :=
    hnum.div hden (fun t ht => by
      rw [Set.mem_Icc] at ht
      have hlp : (0:ℝ) < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
      exact ne_of_gt (pow_pos hlp 2))
  have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => (Real.log t)⁻¹))
      (Set.Icc 2 x) MeasureTheory.volume := by
    have hde : deriv (fun t : ℝ => (Real.log t)⁻¹)
        = fun t => -t⁻¹ / Real.log t ^ 2 :=
      funext fun t => Real.deriv_inv_log_apply
    rw [hde]
    exact hfrac.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_integral_mul₁
    (c := fun k : ℕ => vonMangoldt k / (k:ℝ)) hc0 hc1 x hdiff hint
  have hmain : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ)))
      = (fun t : ℝ => (Real.log t)⁻¹) x
        * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
        - ∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) := hAbel
  have hfx : (fun t : ℝ => (Real.log t)⁻¹) x
        * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
      = 1 + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
        / Real.log x := by
    have hbx : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
        = Real.log x + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
          - Real.log x) := by ring
    conv_lhs => rw [hbx]
    change (Real.log x)⁻¹ * (Real.log x
      + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x))
      = 1 + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
        / Real.log x
    rw [mul_add, inv_mul_cancel₀ hlogx_ne, inv_mul_eq_div]
  have hDlog_int : MeasureTheory.IntegrableOn
      (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
      (Set.Icc 2 x) MeasureTheory.volume := by
    have hcont : ContinuousOn
        (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
        (Set.Icc 2 x) := by
      have hDf : ContinuousOn
          (fun t : ℝ => deriv (fun t : ℝ => (Real.log t)⁻¹) t) (Set.Icc 2 x) := by
        have hde : (fun t : ℝ => deriv (fun t : ℝ => (Real.log t)⁻¹) t)
            = fun t => -t⁻¹ / Real.log t ^ 2 :=
          funext fun t => Real.deriv_inv_log_apply
        rw [hde]
        exact hfrac
      exact hDf.mul (ContinuousOn.log continuousOn_id (fun t ht => by
        rw [Set.mem_Icc] at ht
        exact ne_of_gt (by linarith : (0:ℝ) < t)))
    exact hcont.integrableOn_Icc
  have hwhole : MeasureTheory.IntegrableOn
      (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
        * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
      (Set.Icc 2 x) MeasureTheory.volume :=
    integrableOn_mul_sum_Icc (fun k : ℕ => vonMangoldt k / (k:ℝ))
      (show (0:ℝ) ≤ 2 by norm_num) hint
  have hR_int : MeasureTheory.IntegrableOn
      (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
        * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t))
      (Set.Icc 2 x) MeasureTheory.volume := by
    have heq : (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t))
          = (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
            * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
            - (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t) := by
      funext t
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact hwhole.sub hDlog_int
  have hDlog_Ioc := hDlog_int.mono_set Set.Ioc_subset_Icc_self
  have hwhole_Ioc := hwhole.mono_set Set.Ioc_subset_Icc_self
  have hR_Ioc := hR_int.mono_set Set.Ioc_subset_Icc_self
  have hsplit : (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
        * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
      = (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
        + (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) := by
    have heq : (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
          = (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
            + (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
              * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) := by
      funext t
      simp only [Pi.add_apply]
      ring
    rw [heq]
    exact MeasureTheory.integral_add hDlog_Ioc hR_Ioc
  set IDR : ℝ := (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
    * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) with hIDRdef
  have hDall : ∀ t ∈ Set.Ioc (2:ℝ) x,
      deriv (fun t : ℝ => (Real.log t)⁻¹) t = -t⁻¹ / Real.log t ^ 2 := fun t _ =>
    Real.deriv_inv_log_apply
  have hDlog_pt : ∀ t ∈ Set.Ioc (2:ℝ) x,
      deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t
        = -(1/(t * Real.log t)) := by
    intro t ht
    have ht2 : (2:ℝ) < t ∧ t ≤ x := Set.mem_Ioc.mp ht
    have htpos : (0:ℝ) < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    rw [hDall t ht]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
    have h2ne : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlogne
    field_simp
  have hI1 : (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
      = -((Real.log (Real.log x)) - Real.log (Real.log 2)) := by
    have hcongr : (∫ t in Set.Ioc 2 x,
          deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
        = ∫ t in Set.Ioc 2 x, -(1/(t * Real.log t)) :=
      MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
        (Filter.Eventually.of_forall (fun t ht => hDlog_pt t ht))
    rw [hcongr, MeasureTheory.integral_neg, integral_inv_mul_log_facts_a x hx]
  have hDR_pt : ∀ t ∈ Set.Ioc (2:ℝ) x,
      -((Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
        ≤ deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)
        ∧ deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)
          ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) := by
    intro t ht
    have ht2 : (2:ℝ) < t ∧ t ≤ x := Set.mem_Ioc.mp ht
    have htpos : (0:ℝ) < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    have hDeq : |deriv (fun t : ℝ => (Real.log t)⁻¹) t|
        = 1/(t * Real.log t ^ 2) := by
      rw [hDall t ht, abs_div, abs_neg, abs_inv, abs_of_pos htpos,
        abs_of_nonneg (pow_nonneg (le_of_lt hlogpos) 2)]
      have htne : t ≠ 0 := ne_of_gt htpos
      have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
      have h2ne : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlogne
      field_simp
    have hnn : (0:ℝ) ≤ 1/(t * Real.log t ^ 2) := by
      apply div_nonneg (by norm_num)
      apply mul_nonneg (le_of_lt htpos)
      exact pow_nonneg (le_of_lt hlogpos) 2
    have habs : |deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)|
        ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) := by
      have hRt := hRbound t (by linarith)
      rw [abs_mul, hDeq]
      calc (1/(t * Real.log t ^ 2))
            * |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t|
          = |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t|
            * (1/(t * Real.log t ^ 2)) := by ring
        _ ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) :=
          mul_le_mul_of_nonneg_right hRt hnn
    refine ⟨?_, (abs_le.mp habs).2⟩
    calc -((Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
          ≤ -|deriv (fun t : ℝ => (Real.log t)⁻¹) t
            * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)| := by
          linarith [habs]
      _ ≤ deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t) :=
        neg_abs_le _
  have hCh : MeasureTheory.IntegrableOn
      (fun t => (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
      (Set.Icc 2 x) MeasureTheory.volume := by
    apply ContinuousOn.integrableOn_Icc
    refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact continuousOn_id.mul hden
    · intro t ht
      rw [Set.mem_Icc] at ht
      have htpos : (0:ℝ) < t := by linarith
      have hlp : (0:ℝ) < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
      exact ne_of_gt (mul_pos htpos (pow_pos hlp 2))
  have hCh_Ioc := hCh.mono_set Set.Ioc_subset_Icc_self
  have hval : (∫ t in Set.Ioc 2 x, (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
      = (Real.log 4 + 6) * (1 / Real.log 2 - 1 / Real.log x) := by
    rw [MeasureTheory.integral_const_mul, integral_inv_mul_log_sq_facts_b x hx]
  have hle : (Real.log 4 + 6) * (1 / Real.log 2 - 1 / Real.log x)
      ≤ (Real.log 4 + 6) / Real.log 2 := by
    have h1logx : (0:ℝ) ≤ 1 / Real.log x :=
      div_nonneg (by norm_num) (le_of_lt hlogx_pos)
    calc (Real.log 4 + 6) * (1 / Real.log 2 - 1 / Real.log x)
        = (Real.log 4 + 6) * (1 / Real.log 2)
          - (Real.log 4 + 6) * (1 / Real.log x) := by ring
      _ ≤ (Real.log 4 + 6) * (1 / Real.log 2) :=
        sub_le_self _ (mul_nonneg hCnn h1logx)
      _ = (Real.log 4 + 6) / Real.log 2 := by ring
  have hIDR_le : IDR ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [hIDRdef]
    have hmono := MeasureTheory.setIntegral_mono_on hR_Ioc hCh_Ioc measurableSet_Ioc
      (fun t ht => (hDR_pt t ht).2)
    linarith [hmono, hval, hle]
  have hIDR_ge : -((Real.log 4 + 6) / Real.log 2) ≤ IDR := by
    rw [hIDRdef]
    have hpt : ∀ t ∈ Set.Ioc (2:ℝ) x,
        -(deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t))
          ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) := by
      intro t ht
      have h := (hDR_pt t ht).1
      have h2 := neg_le_neg h
      rwa [neg_neg] at h2
    have hRneg_Ioc : MeasureTheory.IntegrableOn
        (fun t => -(deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)))
        (Set.Ioc 2 x) MeasureTheory.volume := hR_Ioc.neg
    have hmono2 := MeasureTheory.setIntegral_mono_on hRneg_Ioc hCh_Ioc
      measurableSet_Ioc hpt
    have hneg : (∫ t in Set.Ioc 2 x, -(deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)))
        = -(∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) :=
      MeasureTheory.integral_neg _
    linarith [hmono2, hval, hle, hneg]
  have heq : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ)))
      - Real.log (Real.log x)
      = (1 - Real.log (Real.log 2))
        + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x - IDR := by
    have h := hmain
    rw [hfx, hsplit, hI1] at h
    linarith
  have hRx := hRbound x hx1
  have e1 : |1 - Real.log (Real.log 2)| ≤ 1 + |Real.log (Real.log 2)| := by
    calc |1 - Real.log (Real.log 2)| ≤ |1| + |Real.log (Real.log 2)| := abs_sub _ _
      _ = 1 + |Real.log (Real.log 2)| := by rw [abs_one]
  have e2 : |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x|
        / Real.log x ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [div_le_iff₀ hlogx_pos]
    have h1 : (1:ℝ) ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ hlog2_pos, one_mul]
      exact Real.log_le_log (by norm_num) (by linarith)
    calc |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x|
          ≤ Real.log 4 + 6 := hRx
      _ = (Real.log 4 + 6) * 1 := by ring
      _ ≤ (Real.log 4 + 6) * (Real.log x / Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 hCnn
      _ = ((Real.log 4 + 6) / Real.log 2) * Real.log x := by ring
  have e2d : |(((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
        / Real.log x)| ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogx_pos]
    exact e2
  have e3 : |IDR| ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [abs_le]
    exact ⟨hIDR_ge, hIDR_le⟩
  calc |(∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ)))
        - Real.log (Real.log x)|
      = |(1 - Real.log (Real.log 2))
        + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x - IDR| := by
        rw [heq]
    _ ≤ |(1 - Real.log (Real.log 2))
        + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x| + |IDR| :=
      abs_sub _ _
    _ ≤ (|1 - Real.log (Real.log 2)|
        + |(((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x)|) + |IDR| :=
      add_le_add_left (abs_add_le _ _) _
    _ ≤ (1 + |Real.log (Real.log 2)| + (Real.log 4 + 6) / Real.log 2)
        + (Real.log 4 + 6) / Real.log 2 :=
      add_le_add (add_le_add e1 e2d) e3
    _ = 1 + 2 * (Real.log 4 + 6) / Real.log 2 + |Real.log (Real.log 2)| := by
      ring

/-- Mertens' second theorem with the primes indexed by `Icc 1 ⌊x⌋₊`, from the von Mangoldt form
and the prime-power correction. -/
private theorem abs_sum_filter_prime_inv_sub_loglog_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p
        - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C4, hC4⟩ := abs_sum_vonMangoldt_div_mul_log_sub_loglog_le
  refine ⟨C4 + 2, fun x hx => ?_⟩
  set N := ⌊x⌋₊ with hNdef
  set f : ℕ → ℝ := fun n => (Real.log (n : ℝ))⁻¹ * (vonMangoldt n / (n : ℝ))
    with hfdef
  have h4 : |∑ n ∈ Finset.Icc 0 N, f n - Real.log (Real.log x)| ≤ C4 := hC4 x hx
  have hsplit1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 N)
    IsPrimePow f
  have hzero : ∑ n ∈ (Finset.Icc 0 N).filter (fun n => ¬ IsPrimePow n), f n
      = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    have hL : vonMangoldt n = 0 := by
      rw [vonMangoldt_apply, ite_eq_right hn.2]
    simp only [hfdef, hL, zero_div, mul_zero]
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 0 N).filter IsPrimePow) Nat.Prime f
  have eS1 : ((Finset.Icc 0 N).filter IsPrimePow).filter Nat.Prime
      = (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime) := by
    rw [Finset.filter_filter]
  have eS2 : ((Finset.Icc 0 N).filter IsPrimePow).filter (fun n => ¬ Nat.Prime n)
      = (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
    rw [Finset.filter_filter]
  rw [eS1, eS2] at hsplit2
  have hS1 : (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime)
      = (Finset.Icc 1 N).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hN⟩, -, hpp⟩
      exact ⟨⟨hpp.one_le, hN⟩, hpp⟩
    · rintro ⟨⟨h1, hN⟩, hpp⟩
      exact ⟨⟨by omega, hN⟩, hpp.isPrimePow, hpp⟩
  have hS2 : (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
      = (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hN⟩, hpp, hnp⟩
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact not_isPrimePow_zero hpp
      exact ⟨⟨by omega, hN⟩, hpp, hnp⟩
    · rintro ⟨⟨h1, hN⟩, hpp, hnp⟩
      exact ⟨⟨by omega, hN⟩, hpp, hnp⟩
  have hterm1 : ∀ p ∈ (Finset.Icc 0 N).filter
      (fun n => IsPrimePow n ∧ n.Prime), f p = (1 : ℝ) / (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpIcc, -, hpp⟩ := hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      linarith
    have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1)
    simp only [hfdef, vonMangoldt_apply_prime hpp, ← mul_div_assoc,
      inv_mul_cancel₀ hlog]
  have hterm2 : ∀ n ∈ (Finset.Icc 0 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime),
      0 ≤ f n ∧ f n ≤ (1 : ℝ) / (n : ℝ) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnIcc, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff n |>.mp hpp
    have hk1 : 1 ≤ k := hk
    have hpk2 : 2 ≤ p ^ k := by
      calc 2 ≤ p ^ 1 := by rw [pow_one]; exact hp.two_le
        _ ≤ p ^ k := pow_le_pow_right₀ hp.one_le hk1
    have hnpos : (0 : ℝ) < ((p ^ k : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hpk2
      linarith
    have hlogpos : 0 < Real.log ((p ^ k : ℕ) : ℝ) := by
      apply Real.log_pos
      have h2 : (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hpk2
      linarith
    have hlogne : Real.log ((p ^ k : ℕ) : ℝ) ≠ 0 := ne_of_gt hlogpos
    have hLnn : 0 ≤ vonMangoldt (p ^ k) := vonMangoldt_nonneg
    have hLle : vonMangoldt (p ^ k) ≤ Real.log ((p ^ k : ℕ) : ℝ) :=
      vonMangoldt_le_log
    have hlognn : (0 : ℝ) ≤ (Real.log ((p ^ k : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr (le_of_lt hlogpos)
    have hdiv : vonMangoldt (p ^ k) / ((p ^ k : ℕ) : ℝ)
        ≤ Real.log ((p ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ) :=
      (div_le_div_iff_of_pos_right hnpos).mpr hLle
    have h2 : (Real.log ((p ^ k : ℕ) : ℝ))⁻¹
          * (Real.log ((p ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ))
        = 1 / ((p ^ k : ℕ) : ℝ) := by
      rw [← mul_div_assoc, inv_mul_cancel₀ hlogne]
    constructor
    · simp only [hfdef]
      exact mul_nonneg hlognn (div_nonneg hLnn (le_of_lt hnpos))
    · have h1 : f (p ^ k) ≤ (Real.log ((p ^ k : ℕ) : ℝ))⁻¹
          * (Real.log ((p ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ)) := by
        simp only [hfdef]
        exact mul_le_mul_of_nonneg_left hdiv hlognn
      rw [h2] at h1
      exact h1
  have hmem : ∀ n ∈ (Finset.Icc 1 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime),
      n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
    intro n hn
    rw [hS2]
    exact hn
  have h1 : ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime), f n
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p := by
    rw [hS1]
    apply Finset.sum_congr rfl
    intro p hp
    apply hterm1
    rw [hS1]
    exact hp
  have h2 : ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), f n
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        f n := by
    rw [hS2]
  have htot : ∑ n ∈ Finset.Icc 0 N, f n
      = ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime), f n
        + ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n := by
    have h0 : ∑ n ∈ (Finset.Icc 0 N).filter IsPrimePow, f n
        = ∑ n ∈ Finset.Icc 0 N, f n := by
      rw [hzero, add_zero] at hsplit1
      exact hsplit1
    rw [← h0, ← hsplit2]
  have hPE : ∑ n ∈ Finset.Icc 0 N, f n
      = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p)
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n := by
    rw [htot, h1, h2]
  have hEnn : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime), f n := by
    apply Finset.sum_nonneg
    intro n hn
    exact (hterm2 n (hmem n hn)).1
  have hEle : ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime), f n ≤ 2 := by
    calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), f n
        ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          (1 : ℝ) / n :=
          Finset.sum_le_sum (fun n hn => (hterm2 n (hmem n hn)).2)
      _ ≤ 2 := sum_inv_nonprime_primePow_le_two N
  have hdecomp : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x)
      = ((∑ n ∈ Finset.Icc 0 N, f n) - Real.log (Real.log x))
        - ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n := by
    rw [hPE]
    ring
  rw [hdecomp]
  calc |((∑ n ∈ Finset.Icc 0 N, f n) - Real.log (Real.log x))
        - ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n|
      ≤ |∑ n ∈ Finset.Icc 0 N, f n - Real.log (Real.log x)|
        + |∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n| := abs_sub _ _
    _ ≤ C4 + 2 := by
        have habs : |∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => IsPrimePow n ∧ ¬ n.Prime), f n| ≤ 2 := by
          rw [abs_of_nonneg hEnn]
          exact hEle
        linarith [h4, habs]

/-- **Mertens' second theorem**: `∑_{p ≤ x} 1/p = log log x + O(1)`. There is `C` with
`|∑_{p ≤ x} 1/p - log log x| ≤ C` for every real `x ≥ 2`. -/
theorem abs_sum_primesLE_inv_sub_log_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_sum_filter_prime_inv_sub_loglog_le
  exact ⟨C, fun x hx => by simpa [Nat.primesLE_eq_filter_Icc_one, one_div] using hC x hx⟩

end MertensSecond

end Chebyshev
