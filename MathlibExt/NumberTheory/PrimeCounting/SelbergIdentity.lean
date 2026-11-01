/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import MathlibExt.NumberTheory.ArithmeticFunction.VonMangoldtConvolution
import MathlibExt.NumberTheory.PrimeCounting.Mertens

/-!
# Selberg's identity

This file proves Selberg's identity (Selberg's symmetry formula) for Chebyshev's function
`ψ`:
`ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x / n) = 2 x log x + O(x)`.

The proof goes through Selberg's sum `S(x) = ∑_{n ≤ x} ∑_{d ∣ n} μ(d) log²(x / d)`. The
divisor-sum identity `∑_{d ∣ n} μ(d) log²(x / d) = 2 Λ(n) log x + (Λ * Λ)(n) - Λ(n) log n`
for `n > 1` shows `S(x) = ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x / n) + O(x)`. Exchanging the order
of summation and using the harmonic asymptotic `∑_{n ≤ y} 1 / n = log y + γ + O(1 / y)` and
Mertens' first theorem shows `S(x) = 2 x log x + O(x)`.

## Main definitions

* `Chebyshev.selbergSum`: Selberg's sum `S(x) = ∑_{n ≤ x} ∑_{d ∣ n} μ(d) log²(x / d)`.

## Main statements

* `Real.sum_log_div_pow_isBigO`: `∑_{n ≤ x} log^k (x / n) = O(x)`.
* `Chebyshev.sum_vonMangoldt_mul_log_sub_psi_mul_log_isBigO`:
  `∑_{n ≤ x} Λ(n) log n = ψ(x) log x + O(x)`.
* `Chebyshev.selbergSum_sub_psi_mul_log_sub_sum_vonMangoldt_mul_psi_isBigO`:
  `S(x) = ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x / n) + O(x)`.
* `Chebyshev.selbergSum_sub_two_mul_mul_log_isBigO`: `S(x) = 2 x log x + O(x)`.
* `Chebyshev.psi_mul_log_add_sum_vonMangoldt_mul_psi_sub_isBigO`: Selberg's identity.
-/

@[expose] public section

open Finset Filter Asymptotics
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace Real

/-- Logarithmic weights sum linearly: for every `k`,
`∑_{n ≤ x} log^k (x / n) = O(x)` as `x → ∞`. -/
theorem sum_log_div_pow_isBigO (k : ℕ) :
    (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / n) ^ k) =O[atTop] fun x : ℝ => x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [pow_zero, sum_const, Nat.card_Ioc, tsub_zero, nsmul_eq_mul, mul_one,
      Real.norm_natCast, Real.norm_of_nonneg hx, one_mul]
    exact Nat.floor_le hx
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  -- pointwise: `log^k y ≤ (2k)^k √y` for `y ≥ 1`
  have hpt : ∀ y : ℝ, 1 ≤ y → Real.log y ^ k ≤ (2 * k : ℝ) ^ k * √y := by
    intro y hy
    have hε : (0 : ℝ) < 1 / (2 * k) := by positivity
    have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ y) hε
    have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
    have h2 : Real.log y ≤ (2 * k) * y ^ (1 / (2 * k : ℝ)) := by
      calc Real.log y ≤ y ^ (1 / (2 * k : ℝ)) / (1 / (2 * k)) := h1
        _ = (2 * k) * y ^ (1 / (2 * k : ℝ)) := by field_simp
    have h3 : Real.log y ^ k ≤ ((2 * k) * y ^ (1 / (2 * k : ℝ))) ^ k :=
      pow_le_pow_left₀ hlog0 h2 k
    have h4 : (y ^ (1 / (2 * k : ℝ))) ^ k = √y := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      congr 1
      field_simp
    rw [mul_pow, h4] at h3
    exact h3
  -- `∑_{n ≤ N} 1/√n ≤ 2√N`
  have hsum : ∀ N : ℕ, ∑ n ∈ Ioc 0 N, 1 / √(n : ℝ) ≤ 2 * √(N : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
      have hN1 : (0 : ℝ) < √((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hsq : √((N + 1 : ℕ) : ℝ) * √((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
        rw [Real.mul_self_sqrt (by positivity)]; push_cast; ring
      have hsqN : √(N : ℝ) * √(N : ℝ) = (N : ℝ) := Real.mul_self_sqrt (by positivity)
      have hle : √(N : ℝ) ≤ √((N + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
      have key : 1 / √((N + 1 : ℕ) : ℝ) ≤ 2 * √((N + 1 : ℕ) : ℝ) - 2 * √(N : ℝ) := by
        rw [div_le_iff₀ hN1]
        nlinarith [Real.sqrt_nonneg (N : ℝ)]
      linarith
  apply IsBigO.of_bound (2 * (2 * k : ℝ) ^ k)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hmem : ∀ n ∈ Ioc 0 ⌊x⌋₊, 1 ≤ x / n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hnx : (n : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx0.le)
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hterm : ∀ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / n) ^ k ≤
      (2 * k : ℝ) ^ k * √x * (1 / √(n : ℝ)) := by
    intro n hn
    have := hpt _ (hmem n hn)
    rw [Real.sqrt_div' _ (Nat.cast_nonneg n)] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hnonneg : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / n) ^ k :=
    Finset.sum_nonneg fun n hn => pow_nonneg (Real.log_nonneg (hmem n hn)) k
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hx0.le]
  have hfl : √(⌊x⌋₊ : ℝ) ≤ √x := Real.sqrt_le_sqrt (Nat.floor_le hx0.le)
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hC : 0 ≤ (2 * k : ℝ) ^ k * √x := by positivity
  calc ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / n) ^ k
      ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (2 * k : ℝ) ^ k * √x * (1 / √(n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (2 * k : ℝ) ^ k * √x * ∑ n ∈ Ioc 0 ⌊x⌋₊, 1 / √(n : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ (2 * k : ℝ) ^ k * √x * (2 * √x) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith [hsum ⌊x⌋₊]
    _ = 2 * (2 * k : ℝ) ^ k * x := by linear_combination (2 * (2 * k : ℝ) ^ k) * hsx

end Real

namespace Chebyshev

/-- `∑_{n ≤ x} Λ(n) log n = ψ(x) log x + O(x)` as `x → ∞`. -/
theorem sum_vonMangoldt_mul_log_sub_psi_mul_log_isBigO :
    (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n) - ψ x * Real.log x)
      =O[atTop] fun x : ℝ => x := by
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Real.log 4 + 4 := ⟨_, rfl⟩
  have hC0 : (0 : ℝ) < C := by
    rw [hCdef]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
  have hpsi : ∀ M : ℕ, ∑ n ∈ Ioc 0 M, Λ n = ψ (M : ℝ) := by
    intro M
    rw [Chebyshev.psi, Nat.floor_natCast]
  have hpsibd : ∀ M : ℕ, ∑ n ∈ Ioc 0 M, Λ n ≤ C * M := by
    intro M
    rw [hpsi M, hCdef]
    exact Chebyshev.psi_le_const_mul_self (by positivity)
  have hsumnn : ∀ M : ℕ, (0 : ℝ) ≤ ∑ n ∈ Ioc 0 M, Λ n :=
    fun M => Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  -- Discrete partial summation: `∑_{n ≤ M} Λ n (log M - log n) = ∑_{m < M} ψ m log (1 + 1/m)`,
  -- and each of the `M` increments is at most `ψ m / m ≤ C`.
  have key : ∀ M : ℕ, ∑ n ∈ Ioc 0 M, Λ n * (Real.log M - Real.log n) ≤ C * M := by
    intro M
    induction M with
    | zero => simp
    | succ K ih =>
      push_cast
      have hstep : ∑ n ∈ Ioc 0 (K + 1), Λ n * (Real.log ((K : ℝ) + 1) - Real.log n)
          = (∑ n ∈ Ioc 0 K, Λ n * (Real.log K - Real.log n))
            + (Real.log ((K : ℝ) + 1) - Real.log K) * (∑ n ∈ Ioc 0 K, Λ n) := by
        rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
        rw [Finset.sum_congr rfl (fun n _ => by ring :
          ∀ n ∈ Ioc 0 K, Λ n * (Real.log ((K : ℝ) + 1) - Real.log n)
            = Λ n * (Real.log K - Real.log n)
              + (Real.log ((K : ℝ) + 1) - Real.log K) * Λ n)]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        push_cast
        ring
      have hinc : (Real.log ((K : ℝ) + 1) - Real.log K) * (∑ n ∈ Ioc 0 K, Λ n) ≤ C := by
        rcases Nat.eq_zero_or_pos K with rfl | hK
        · simp [hC0.le]
        · have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
          have hlogd : Real.log ((K : ℝ) + 1) - Real.log K ≤ 1 / K := by
            have h1 : Real.log (((K : ℝ) + 1) / K) ≤ ((K : ℝ) + 1) / K - 1 :=
              Real.log_le_sub_one_of_pos (by positivity)
            rw [Real.log_div (by positivity) (by positivity)] at h1
            have h2 : ((K : ℝ) + 1) / K - 1 = 1 / K := by field_simp; ring
            linarith [h1, h2.le, h2.ge]
          calc (Real.log ((K : ℝ) + 1) - Real.log K) * (∑ n ∈ Ioc 0 K, Λ n)
              ≤ (1 / (K : ℝ)) * (C * K) :=
                mul_le_mul hlogd (hpsibd K) (hsumnn K) (by positivity)
            _ = C := by field_simp
      rw [hstep]
      linarith
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * C, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := by rw [hNdef]; exact Nat.floor_le (by linarith)
  have hpsix : ψ x = ∑ n ∈ Ioc 0 N, Λ n := rfl
  have hA : ∑ n ∈ Ioc 0 N, Λ n * (Real.log x - Real.log n)
      = ψ x * Real.log x - ∑ n ∈ Ioc 0 N, Λ n * Real.log n := by
    rw [hpsix, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hAnn : 0 ≤ ∑ n ∈ Ioc 0 N, Λ n * (Real.log x - Real.log n) := by
    refine Finset.sum_nonneg fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn.2) hNx
    have hlog : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
    have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith
  have hsplit : ∑ n ∈ Ioc 0 N, Λ n * (Real.log x - Real.log n)
      = (Real.log x - Real.log N) * (∑ n ∈ Ioc 0 N, Λ n)
        + ∑ n ∈ Ioc 0 N, Λ n * (Real.log N - Real.log n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hlogd : Real.log x - Real.log N ≤ 1 / N := by
    have h1 : Real.log (x / N) ≤ x / N - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (by positivity)] at h1
    have hxN : x < (N : ℝ) + 1 := by rw [hNdef]; exact Nat.lt_floor_add_one x
    have h2 : x / (N : ℝ) - 1 ≤ 1 / N := by
      rw [sub_le_iff_le_add, div_le_iff₀ hNpos]
      have h3 : (1 / (N : ℝ) + 1) * N = 1 + N := by field_simp
      rw [h3]; linarith
    linarith
  have hprod : (Real.log x - Real.log N) * (∑ n ∈ Ioc 0 N, Λ n) ≤ C := by
    calc (Real.log x - Real.log N) * (∑ n ∈ Ioc 0 N, Λ n)
        ≤ (1 / (N : ℝ)) * (C * N) := mul_le_mul hlogd (hpsibd N) (hsumnn N) (by positivity)
      _ = C := by field_simp
  have hT : ∑ n ∈ Ioc 0 N, Λ n * (Real.log N - Real.log n) ≤ C * x :=
    le_trans (key N) (mul_le_mul_of_nonneg_left hNx hC0.le)
  have hCx : C ≤ C * x := le_mul_of_one_le_right hC0.le (by linarith)
  have hle : ∑ n ∈ Ioc 0 N, Λ n * (Real.log x - Real.log n) ≤ 2 * C * x := by
    rw [hsplit]; linarith
  have hDval : (∑ n ∈ Ioc 0 N, Λ n * Real.log n) - ψ x * Real.log x
      = -(∑ n ∈ Ioc 0 N, Λ n * (Real.log x - Real.log n)) := by
    rw [hA]; ring
  rw [hDval, norm_neg, Real.norm_eq_abs, abs_of_nonneg hAnn, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
  exact hle

/-- **Selberg's sum** `S(x) = ∑_{n ≤ x} ∑_{d ∣ n} μ(d) log²(x / d)`, the auxiliary sum in
the elementary proof of Selberg's identity. Its inner weight depends on `x` as well as on
`d`, so `S` is not the summatory function of a fixed arithmetic function. -/
noncomputable def selbergSum (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log (x / d) ^ 2

/-- Grouping a summatory divisor sum by the divisor:
`∑_{n ≤ N} ∑_{d ∣ n} g(d) = ∑_{d ≤ N} g(d) ⌊N / d⌋`. -/
private lemma sum_Ioc_sum_divisors_eq_sum_Ioc_mul (N : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d = ∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) := by
  let F : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else g d, by simp⟩
  have hF : ∀ d, d ≠ 0 → F d = g d := fun d hd => ite_eq_right hd
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum F N
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  calc ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d
      = ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, F d := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun d hd => ?_
        exact (hF d (Nat.pos_of_mem_divisors hd).ne').symm
    _ = ∑ d ∈ Ioc 0 N, F d * ((N / d : ℕ) : ℝ) := h
    _ = _ := Finset.sum_congr rfl fun d hd => by rw [hF d (Finset.mem_Ioc.mp hd).1.ne']

/-- `S(x) = ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x / n) + O(x)` as `x → ∞`. -/
theorem selbergSum_sub_psi_mul_log_sub_sum_vonMangoldt_mul_psi_isBigO :
    (fun x : ℝ => selbergSum x - (ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n)))
      =O[atTop] fun x : ℝ => x := by
  have hident : ∀ x : ℝ, 1 ≤ x →
      selbergSum x - (ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n))
        = Real.log x ^ 2 - ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log n) - ψ x * Real.log x) := by
    intro x hx
    have hx0 : x ≠ 0 := by positivity
    have hN1 : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
    have hconv : ∑ n ∈ Ioc 0 ⌊x⌋₊, (Λ * Λ) n = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) := by
      rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Chebyshev.psi, Nat.floor_div_natCast]
    unfold selbergSum
    simp_rw [ArithmeticFunction.sum_divisors_moebius_mul_log_div_sq hx0]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hconv,
      Finset.sum_ite_eq' (Ioc 0 ⌊x⌋₊) 1, ite_eq_left (Finset.mem_Ioc.mpr ⟨one_pos, hN1⟩)]
    have hψ : ∑ n ∈ Ioc 0 ⌊x⌋₊, 2 * Λ n * Real.log x = 2 * ψ x * Real.log x := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rfl
    rw [hψ]
    ring
  have hlog : (fun x : ℝ => Real.log x ^ 2) =O[atTop] fun x : ℝ => x :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).isBigO
  refine ((hlog.sub sum_vonMangoldt_mul_log_sub_psi_mul_log_isBigO).congr' ?_
    (EventuallyEq.refl _ _))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (hident x hx).symm

/-- Selberg's sum as a Möbius sum over `⌊x / d⌋`:
`S(x) - γ² = ∑_{d ≤ x} μ(d) ⌊x / d⌋ (log²(x / d) - γ²)` for `x ≥ 1`. -/
private lemma selbergSum_sub_eulerMascheroniConstant_sq (x : ℝ) (hx : 1 ≤ x) :
    selbergSum x - Real.eulerMascheroniConstant ^ 2
      = ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) * (⌊x / d⌋₊ : ℝ)
          * (Real.log (x / d) ^ 2 - Real.eulerMascheroniConstant ^ 2) := by
  have hN : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hfl : ∀ d : ℕ, ((⌊x⌋₊ / d : ℕ) : ℝ) = (⌊x / d⌋₊ : ℝ) := fun d => by
    rw [Nat.floor_div_natCast]
  have h1 : selbergSum x
      = ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) * Real.log (x / d) ^ 2 * ((⌊x⌋₊ / d : ℕ) : ℝ) :=
    sum_Ioc_sum_divisors_eq_sum_Ioc_mul _ _
  have h2 : ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) * ((⌊x⌋₊ / d : ℕ) : ℝ) = 1 := by
    rw [← sum_Ioc_sum_divisors_eq_sum_Ioc_mul ⌊x⌋₊ fun d => (μ d : ℝ)]
    simp_rw [ArithmeticFunction.sum_divisors_moebius]
    rw [Finset.sum_ite_eq' (Ioc 0 ⌊x⌋₊) 1, ite_eq_left (Finset.mem_Ioc.mpr ⟨one_pos, hN⟩)]
  have key : ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) * (⌊x / d⌋₊ : ℝ)
        * (Real.log (x / d) ^ 2 - Real.eulerMascheroniConstant ^ 2)
      = (∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) * Real.log (x / d) ^ 2 * ((⌊x⌋₊ / d : ℕ) : ℝ))
        - Real.eulerMascheroniConstant ^ 2
          * (∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) * ((⌊x⌋₊ / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hfl d]
    ring
  rw [key, h2, ← h1]
  ring

/-- `S(x) = x ∑_{d ≤ x} μ(d) / d (log²(x / d) - γ²) + O(x)`. -/
private lemma selbergSum_sub_mul_sum_moebius_div_isBigO :
    (fun x : ℝ => selbergSum x
        - x * ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / (d : ℝ)
            * (Real.log (x / d) ^ 2 - Real.eulerMascheroniConstant ^ 2))
      =O[atTop] fun x : ℝ => x := by
  have hL := Real.sum_log_div_pow_isBigO 2
  set γ := Real.eulerMascheroniConstant
  have hB : (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / (n : ℝ)) ^ 2
      + 2 * γ ^ 2 * x) =O[atTop] fun x : ℝ => x :=
    hL.add ((isBigO_refl (fun x : ℝ => x) atTop).const_mul_left (2 * γ ^ 2))
  refine IsBigO.trans ?_ hB
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hS := selbergSum_sub_eulerMascheroniConstant_sq x hx
  have hdiff : selbergSum x
      - x * ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) ^ 2 - γ ^ 2)
      = γ ^ 2 + ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ)
          * ((⌊x / d⌋₊ : ℝ) - x / d) * (Real.log (x / d) ^ 2 - γ ^ 2) := by
    rw [show selbergSum x = γ ^ 2 + (selbergSum x - γ ^ 2) by ring, hS, Finset.mul_sum,
      add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hterm : ∀ d ∈ Ioc 0 ⌊x⌋₊, |(μ d : ℝ)
      * ((⌊x / d⌋₊ : ℝ) - x / d) * (Real.log (x / d) ^ 2 - γ ^ 2)|
      ≤ Real.log (x / d) ^ 2 + γ ^ 2 := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
    have hxd : 0 ≤ x / d := div_nonneg hx0 (by linarith)
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hfl : |(⌊x / d⌋₊ : ℝ) - x / d| ≤ 1 := by
      rw [abs_le]
      constructor
      · linarith [Nat.lt_floor_add_one (x / d)]
      · linarith [Nat.floor_le hxd]
    have hL2 : |Real.log (x / d) ^ 2 - γ ^ 2| ≤ Real.log (x / d) ^ 2 + γ ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.log (x / d)), sq_nonneg γ]
    rw [abs_mul, abs_mul]
    calc |(μ d : ℝ)| * |(⌊x / d⌋₊ : ℝ) - x / d| * |Real.log (x / d) ^ 2 - γ ^ 2|
        ≤ 1 * 1 * (Real.log (x / d) ^ 2 + γ ^ 2) := by gcongr
      _ = _ := by ring
  have hcard : ((Ioc 0 ⌊x⌋₊).card : ℝ) ≤ x := by
    simp only [Nat.card_Ioc, tsub_zero]
    exact Nat.floor_le hx0
  have hsumle := Finset.abs_sum_le_sum_abs (fun d => (μ d : ℝ)
      * ((⌊x / d⌋₊ : ℝ) - x / d) * (Real.log (x / d) ^ 2 - γ ^ 2)) (Ioc 0 ⌊x⌋₊)
  have hsum2 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum2
  have hpos : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / (n : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hγ : 0 ≤ γ ^ 2 := sq_nonneg _
  rw [hdiff, Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ _ + 2 * γ ^ 2 * x)]
  calc |γ ^ 2 + _| ≤ |γ ^ 2| + |_| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hγ]
      nlinarith [mul_le_mul_of_nonneg_left hcard hγ]

/-- Pointwise harmonic comparison: `|log y + γ - ∑_{e ≤ y} 1 / e| ≤ 2 / y` for `y ≥ 1`. -/
private lemma abs_log_add_eulerMascheroniConstant_sub_sum_le {y : ℝ} (hy : 1 ≤ y) :
    |Real.log y + Real.eulerMascheroniConstant - ∑ e ∈ Ioc 0 ⌊y⌋₊, (1 : ℝ) / e| ≤ 2 / y := by
  set γ := Real.eulerMascheroniConstant with hγdef
  set m := ⌊y⌋₊ with hmdef
  have hm1 : 1 ≤ m := Nat.le_floor (by simpa using hy)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmy : (m : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hym : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
  have hH : (∑ e ∈ Ioc 0 m, (1 : ℝ) / e) = (harmonic m : ℝ) := by
    rw [harmonic_eq_sum_Icc, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
    push_cast
    simp [one_div]
  have h1 : (harmonic m : ℝ) - Real.log ((m : ℝ) + 1) < γ := by
    have := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant m
    simpa [Real.eulerMascheroniSeq, hγdef] using this
  have h2 : γ < (harmonic m : ℝ) - Real.log (m : ℝ) := by
    have := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' m
    have hm0' : m ≠ 0 := by omega
    simpa [Real.eulerMascheroniSeq', hm0', hγdef] using this
  have hlog : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have hrw : ((m : ℝ) + 1) / (m : ℝ) = 1 + 1 / (m : ℝ) := by field_simp
    rw [hrw]
    simpa using Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (m : ℝ) by positivity)
  have hl1 : Real.log (m : ℝ) ≤ Real.log y := Real.log_le_log hm0 hmy
  have hl2 : Real.log y ≤ Real.log ((m : ℝ) + 1) := Real.log_le_log (by linarith) hym.le
  have h2y : 1 / (m : ℝ) ≤ 2 / y := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    rw [div_le_div_iff₀ hm0 (by linarith)]; linarith
  rw [hH]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S(x) / x = ∑_{d ≤ x} μ(d) / d (log(x / d) - γ) ∑_{e ≤ x / d} 1 / e + O(1)`. -/
private lemma selbergSum_div_sub_sum_moebius_div_mul_harmonic_isBigO :
    (fun x : ℝ => selbergSum x / x
        - ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) - Real.eulerMascheroniConstant)
            * ∑ e ∈ Ioc 0 ⌊x / (d : ℝ)⌋₊, (1 : ℝ) / e)
      =O[atTop] fun _ : ℝ => (1 : ℝ) := by
  set γ := Real.eulerMascheroniConstant with hγdef
  obtain ⟨CA, hCA⟩ := selbergSum_sub_mul_sum_moebius_div_isBigO.bound
  obtain ⟨CB, hCB⟩ := (Real.sum_log_div_pow_isBigO 1).bound
  rw [Asymptotics.isBigO_iff]
  refine ⟨CA + 2 * CB + 2 * |γ|, ?_⟩
  filter_upwards [hCA, hCB, eventually_ge_atTop (1 : ℝ)] with x hA hB hx
  have hx0 : (0 : ℝ) < x := by linarith
  set N := ⌊x⌋₊ with hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  -- the error per `d`
  set E : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) - γ)
    * (Real.log (x / d) + γ - ∑ e ∈ Ioc 0 ⌊x / (d : ℝ)⌋₊, (1 : ℝ) / e) with hEdef
  have hsplit : selbergSum x / x
      - ∑ d ∈ Ioc 0 N, (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) - γ)
          * ∑ e ∈ Ioc 0 ⌊x / (d : ℝ)⌋₊, (1 : ℝ) / e
      = (selbergSum x - x * ∑ d ∈ Ioc 0 N, (μ d : ℝ) / (d : ℝ)
            * (Real.log (x / d) ^ 2 - γ ^ 2)) / x + ∑ d ∈ Ioc 0 N, E d := by
    rw [sub_div, mul_div_cancel_left₀ _ hx0.ne', hEdef]
    simp only
    have hrw : ∑ d ∈ Ioc 0 N, (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) - γ)
          * (Real.log (x / d) + γ - ∑ e ∈ Ioc 0 ⌊x / (d : ℝ)⌋₊, (1 : ℝ) / e)
        = ∑ d ∈ Ioc 0 N, (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) ^ 2 - γ ^ 2)
          - ∑ d ∈ Ioc 0 N, (μ d : ℝ) / (d : ℝ)
            * (Real.log (x / d) - γ) * ∑ e ∈ Ioc 0 ⌊x / (d : ℝ)⌋₊, (1 : ℝ) / e := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [hrw]
    ring
  have hEb : ∀ d ∈ Ioc 0 N, |E d| ≤ 2 / x * (Real.log (x / d) ^ 1 + |γ|) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
    have hdx : (d : ℝ) ≤ x := le_trans (by exact_mod_cast (Finset.mem_Ioc.mp hd).2) hNx
    have hy : 1 ≤ x / d := by rw [le_div_iff₀ hd0]; linarith
    have hL : 0 ≤ Real.log (x / d) := Real.log_nonneg hy
    have hh := abs_log_add_eulerMascheroniConstant_sub_sum_le hy
    have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hLg : |Real.log (x / d) - γ| ≤ Real.log (x / d) + |γ| := by
      calc |Real.log (x / d) - γ| ≤ |Real.log (x / d)| + |γ| := abs_sub _ _
        _ = Real.log (x / d) + |γ| := by rw [abs_of_nonneg hL]
    have h2 : 2 / (x / d) = (d : ℝ) * (2 / x) := by field_simp
    rw [hEdef]
    simp only
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hd0, pow_one]
    calc |(μ d : ℝ)| / d * |Real.log (x / d) - γ|
          * |Real.log (x / d) + γ - ∑ e ∈ Ioc 0 ⌊x / (d : ℝ)⌋₊, (1 : ℝ) / e|
        ≤ 1 / d * (Real.log (x / d) + |γ|) * (d * (2 / x)) := by
          rw [← h2]
          gcongr
      _ = 2 / x * (Real.log (x / d) + |γ|) := by field_simp
  have hEsum : |∑ d ∈ Ioc 0 N, E d|
      ≤ 2 / x * (∑ n ∈ Ioc 0 N, Real.log (x / (n : ℝ)) ^ 1) + 2 / x * (N * |γ|) := by
    calc |∑ d ∈ Ioc 0 N, E d| ≤ ∑ d ∈ Ioc 0 N, |E d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 N, 2 / x * (Real.log (x / d) ^ 1 + |γ|) := Finset.sum_le_sum hEb
      _ = _ := by
        rw [← mul_add, ← Finset.mul_sum, Finset.sum_add_distrib]
        simp
  have hBn : 0 ≤ ∑ n ∈ Ioc 0 N, Real.log (x / (n : ℝ)) ^ 1 := by
    refine Finset.sum_nonneg fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (Finset.mem_Ioc.mp hn).2) hNx
    rw [pow_one]
    exact Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hBn, Real.norm_eq_abs, abs_of_pos hx0] at hB
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0] at hA
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one, hsplit]
  have hA' : |(selbergSum x - x * ∑ d ∈ Ioc 0 N, (μ d : ℝ)
      / (d : ℝ) * (Real.log (x / d) ^ 2 - γ ^ 2)) / x| ≤ CA := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; exact hA
  have hB' : 2 / x * (∑ n ∈ Ioc 0 N, Real.log (x / (n : ℝ)) ^ 1) ≤ 2 * CB := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx0]; linarith
  have hG : 2 / x * (N * |γ|) ≤ 2 * |γ| := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx0]
    nlinarith [abs_nonneg γ]
  have hsum := abs_add_le ((selbergSum x - x * ∑ d ∈ Ioc 0 N,
      (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) ^ 2 - γ ^ 2)) / x) (∑ d ∈ Ioc 0 N, E d)
  linarith

/-- `S(x) = 2 x log x + O(x)` as `x → ∞`. -/
theorem selbergSum_sub_two_mul_mul_log_isBigO :
    (fun x : ℝ => selbergSum x - 2 * x * Real.log x) =O[atTop] fun x : ℝ => x := by
  set γ := Real.eulerMascheroniConstant with hγdef
  -- The double sum of the previous lemma is `∑_{n ≤ x} Λ(n) / n + log x - γ`.
  have key : ∀ x : ℝ, 1 ≤ x →
      ∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) - γ)
          * ∑ e ∈ Ioc 0 ⌊x / (d : ℝ)⌋₊, (1 : ℝ) / e
        = (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ)) + Real.log x - γ := by
    intro x hx
    have hx0 : x ≠ 0 := by positivity
    let F : ArithmeticFunction ℝ :=
      ⟨fun d => (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) - γ), by simp⟩
    let G : ArithmeticFunction ℝ := ⟨fun e => (1 : ℝ) / e, by simp⟩
    have hFG := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum F G ⌊x⌋₊
    simp_rw [Nat.floor_div_natCast]
    change _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, F n * ∑ m ∈ Ioc 0 (⌊x⌋₊ / n), G m at hFG
    change ∑ d ∈ Ioc 0 ⌊x⌋₊, F d * ∑ e ∈ Ioc 0 (⌊x⌋₊ / d), G e = _
    rw [← hFG]
    have hterm : ∀ r ∈ Ioc 0 ⌊x⌋₊,
        (F * G) r = Λ r / (r : ℝ) + (if r = 1 then Real.log x - γ else 0) := by
      intro r hr
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hr).1.ne'
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => F i * G j)]
      have hstep : ∀ d ∈ r.divisors, F d * G (r / d)
          = (1 / (r : ℝ)) * ((Real.log x - γ) * (μ d : ℝ) - (μ d : ℝ) * Real.log d) := by
        intro d hd
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
        change (μ d : ℝ) / (d : ℝ) * (Real.log (x / d) - γ) * ((1 : ℝ) / ((r / d : ℕ) : ℝ)) = _
        rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0, Real.log_div hx0 hd0]
        field_simp
        ring
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ArithmeticFunction.sum_divisors_moebius]
      have hlog : ∑ d ∈ r.divisors, (μ d : ℝ) * Real.log d = -Λ r := by
        simpa [ArithmeticFunction.log_apply] using
          ArithmeticFunction.sum_moebius_mul_log_eq (n := r)
      rw [hlog]
      split_ifs with h
      · subst h; simp
      · field_simp
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' _ 1,
      ite_eq_left (Finset.mem_Ioc.mpr ⟨one_pos, Nat.floor_pos.mpr hx⟩)]
    ring
  have h7 := selbergSum_div_sub_sum_moebius_div_mul_harmonic_isBigO
  have hM := sum_vonMangoldt_div_sub_log_isBigO_one
  have hc : (fun _ : ℝ => -γ) =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    isBigO_const_const _ one_ne_zero _
  have h8 : (fun x : ℝ => selbergSum x / x - 2 * Real.log x) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
    refine ((h7.add hM).add hc).congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [key x hx]
    ring
  refine (h8.mul (isBigO_refl (fun x : ℝ => x) atTop)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  · exact Eventually.of_forall fun x => by simp

/-- **Selberg's identity** (Selberg's symmetry formula):
`ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x / n) = 2 x log x + O(x)` as `x → ∞`. -/
theorem psi_mul_log_add_sum_vonMangoldt_mul_psi_sub_isBigO :
    (fun x : ℝ => ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) - 2 * x * Real.log x)
      =O[atTop] fun x : ℝ => x :=
  (selbergSum_sub_two_mul_mul_log_isBigO.sub
    selbergSum_sub_psi_mul_log_sub_sum_vonMangoldt_mul_psi_isBigO).congr'
    (Eventually.of_forall fun x => by ring) (Eventually.of_forall fun _ => rfl)

end Chebyshev
