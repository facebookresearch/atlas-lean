/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Sieve.Basic
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.NumberTheory.PrimeCounting.Mertens
import MathlibExt.NumberTheory.PrimeCounting.AverageOmegaHFree

/-!
# Rankin's trick

Rankin's trick bounds a sum over integers `d ≤ t` with prime factors `≤ z` by inserting the
weight `(t / d)^δ ≥ 1` and extending the sum to all such `d`, which then factors as an Euler
product. Taking `δ = 1 - 1 / log z` and using Mertens' theorems gives the saving
`exp(-log t / log z)`.

## Main statements

* `Nat.sum_primesLE_inv_le_log_log_add`: Mertens' second theorem as a uniform upper bound,
  `∑_{p ≤ z} 1/p ≤ log log z + C`.
* `Real.rpow_inv_log_sub_one_le`: the elementary estimate
  `p^{1/log z - 1} ≤ 1/p + e log p / (p log z)` for `1 ≤ p ≤ z`.
* `Nat.card_smoothNumbersUpTo_le_rpow_mul_prod`: the number of `k`-smooth `n ≤ N` is at most
  `N^δ ∏_{p < k} (1 - p^{-δ})⁻¹`.
* `Nat.card_smoothNumbersUpTo_le_mul_log_mul_exp`: the number of `n ≤ x` with all prime
  factors `≤ z` is `O(x log z · exp(-log x / log z))`, uniformly in `x ≥ 1`, `z ≥ 3`.
* `Nat.sum_divisors_siftingPrimorial_le`: Rankin's bound for a multiplicative weight `ω` of
  sieve dimension `κ`: `∑_{d ∣ P(z), d ≤ t} ω(d) ≪ t (log z)^κ exp(-log t / log z)`.
* `Nat.sum_divisors_siftingPrimorial_div_le`: the corresponding tail bound
  `∑_{d ∣ P(z), d > c x} ω(d)/d ≪ (log z)^{κ+1} exp(-log x / log z)`.
-/

@[expose] public section

open Finset

namespace Nat

/-- `primesLE N` is the set of primes in `[1, N]`. -/
theorem primesLE_eq_filter_Icc (N : ℕ) : N.primesLE = (Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [mem_primesLE, mem_filter, mem_Icc]
  exact ⟨fun h => ⟨⟨h.2.one_lt.le, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

/-- **Mertens' second theorem**, as a uniform upper bound: there is `C` with
`∑_{p ≤ z} 1/p ≤ log log z + C` for every real `z ≥ 2`. -/
theorem sum_primesLE_inv_le_log_log_add :
    ∃ C : ℝ, ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ primesLE ⌊z⌋₊, (p : ℝ)⁻¹ ≤ Real.log (Real.log z) + C := by
  obtain ⟨C, hC⟩ := MetaMathlibExt.abs_sum_prime_inv_sub_loglog_le
  refine ⟨C, fun z hz => ?_⟩
  have h := (abs_le.mp (hC z hz)).2
  rw [primesLE_eq_filter_Icc]
  simp only [one_div] at h
  linarith

end Nat

namespace Real

/-- For `1 ≤ p ≤ z` with `log z > 0`, `p^{1/log z - 1} ≤ 1/p + e · (1/log z) · (log p / p)`.
This is the elementary estimate behind Rankin's trick with `δ = 1 - 1/log z`. -/
theorem rpow_inv_log_sub_one_le {p z : ℝ} (hp : 1 ≤ p) (hpz : p ≤ z) (hz : 0 < Real.log z) :
    p ^ (1 / Real.log z - 1) ≤ p⁻¹ + Real.exp 1 * (1 / Real.log z) * (Real.log p / p) := by
  have hp0 : 0 < p := by linarith
  set η := 1 / Real.log z with hη
  have hη0 : 0 < η := by positivity
  have heq : p ^ (η - 1) = p⁻¹ * Real.exp (η * Real.log p) := by
    rw [Real.rpow_def_of_pos hp0]
    conv_rhs => rw [← Real.exp_log hp0, ← Real.exp_neg, ← Real.exp_add]
    rw [Real.log_exp]
    congr 1; ring
  have hv0 : 0 ≤ η * Real.log p := mul_nonneg hη0.le (Real.log_nonneg hp)
  have hv1 : η * Real.log p ≤ 1 := by
    rw [hη, one_div_mul_eq_div, div_le_one hz]
    exact Real.log_le_log hp0 hpz
  have h1 := Real.add_one_le_exp (-(η * Real.log p))
  have h2 : Real.exp (η * Real.log p) ≤ Real.exp 1 := Real.exp_le_exp.mpr hv1
  have h3 : Real.exp (-(η * Real.log p)) * Real.exp (η * Real.log p) = 1 := by
    rw [← Real.exp_add]; simp
  have hev : Real.exp (η * Real.log p) ≤ 1 + Real.exp 1 * (η * Real.log p) := by
    nlinarith [mul_le_mul_of_nonneg_right h1 (Real.exp_pos (η * Real.log p)).le,
      mul_le_mul_of_nonneg_left h2 hv0]
  rw [heq]
  calc p⁻¹ * Real.exp (η * Real.log p) ≤ p⁻¹ * (1 + Real.exp 1 * (η * Real.log p)) := by
        gcongr
    _ = p⁻¹ + Real.exp 1 * η * (Real.log p / p) := by field_simp

end Real

namespace Nat

/-- **Rankin's trick** for smooth numbers: for every `δ > 0`, the number of `k`-smooth
`n ≤ N` is at most `N^δ ∏_{p < k} (1 - p^{-δ})⁻¹`. -/
theorem card_smoothNumbersUpTo_le_rpow_mul_prod (N k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ((N.smoothNumbersUpTo k).card : ℝ) ≤
      (N : ℝ) ^ δ * ∏ p ∈ k.primesBelow, (1 - (p : ℝ) ^ (-δ))⁻¹ := by
  set S := N.smoothNumbersUpTo k with hS
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-δ)
      map_one' := by simp
      map_mul' := fun a b => by
        push_cast
        exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) }
  have hf : ∀ n : ℕ, f n = (n : ℝ) ^ (-δ) := fun n => rfl
  have hlt : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := by
    intro p hp
    rw [hf, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hlt k).2
  have h1 : ∑ m ∈ S.subtype (· ∈ k.smoothNumbers), f m ≤ ∏ p ∈ k.primesBelow, (1 - f p)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by rw [hf]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum
  rw [Finset.sum_subtype_eq_sum_filter] at h1
  have hfil : S.filter (· ∈ k.smoothNumbers) = S :=
    Finset.filter_true_of_mem fun n hn => (Nat.mem_smoothNumbersUpTo.mp hn).2
  rw [hfil] at h1
  have h2 : (S.card : ℝ) ≤ ∑ n ∈ S, (N : ℝ) ^ δ * f n := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Nat.mem_smoothNumbersUpTo.mp hn
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero (ne_zero_of_mem_smoothNumbers hn2)
    have hnx : (n : ℝ) ≤ N := by exact_mod_cast hn1
    rw [hf, Real.rpow_neg hnpos.le, Nat.cast_one, ← div_eq_mul_inv,
      one_le_div (Real.rpow_pos_of_pos hnpos _)]
    exact Real.rpow_le_rpow hnpos.le hnx hδ.le
  rw [← Finset.mul_sum] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The number `Ψ(x, z)` of `n ≤ x` all of whose prime factors are `≤ z` satisfies
`Ψ(x, z) ≪ x (log z) exp(-log x / log z)`, uniformly in `x ≥ 1` and `z ≥ 3`. -/
theorem card_smoothNumbersUpTo_le_mul_log_mul_exp :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ z : ℝ, 3 ≤ z →
      ((⌊x⌋₊.smoothNumbersUpTo (⌊z⌋₊ + 1)).card : ℝ) ≤
        C * x * Real.log z * Real.exp (-(Real.log x / Real.log z)) := by
  obtain ⟨C₁, hMert⟩ := sum_primesLE_inv_le_log_log_add
  set B := Real.log 4 + 6 with hB
  have hB0 : 0 ≤ B := by positivity
  have hS2 : ∃ M : ℝ, ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, ((p : ℝ) ^ 2)⁻¹ ≤ M := by
    refine ⟨∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹, fun N => ?_⟩
    exact (Real.summable_nat_pow_inv.mpr (by norm_num)).sum_le_tsum _
      (fun i _ => by positivity)
  obtain ⟨M, hM⟩ := hS2
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  set δ₀ := 1 - 1 / Real.log 3 with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀, sub_pos, div_lt_one (by linarith)]; exact hlog3
  set a := (2 : ℝ) ^ (-δ₀) with ha
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K := (1 - a)⁻¹ with hK
  have hK0 : 0 < K := by rw [hK]; apply inv_pos.mpr; linarith
  set E := Real.exp 1 with hE
  have hE0 : 0 < E := Real.exp_pos 1
  refine ⟨Real.exp (C₁ + E + E * B + K * E ^ 2 * M), ?_⟩
  intro x hx z hz
  have hlz : 1 < Real.log z := hlog3.trans_le (Real.log_le_log (by norm_num) hz)
  have hlz0 : 0 < Real.log z := by linarith
  set η := 1 / Real.log z with hη
  have hη0 : 0 < η := by positivity
  set δ := 1 - η with hδ
  have hδ₀le : δ₀ ≤ δ := by
    rw [hδ, hδ₀, hη]
    have : 1 / Real.log z ≤ 1 / Real.log 3 :=
      one_div_le_one_div_of_le (by linarith) (Real.log_le_log (by norm_num) hz)
    linarith
  have hδpos : 0 < δ := by linarith
  have hx0 : 0 < x := by linarith
  have h5 : ((⌊x⌋₊.smoothNumbersUpTo (⌊z⌋₊ + 1)).card : ℝ) ≤
      x ^ δ * ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ) ^ (-δ))⁻¹ :=
    (card_smoothNumbersUpTo_le_rpow_mul_prod _ _ hδpos).trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0.le)
        hδpos.le) (Finset.prod_nonneg fun p hp => by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
          have : (p : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
            (by linarith)
          have : 0 < 1 - (p : ℝ) ^ (-δ) := by linarith
          positivity))
  have hxδ : x ^ δ = x * Real.exp (-(Real.log x / Real.log z)) := by
    rw [Real.rpow_def_of_pos hx0, hδ, hη]
    conv_rhs => rw [← Real.exp_log hx0]
    rw [← Real.exp_add, Real.log_exp]
    congr 1
    ring
  have hz1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hprime : ∀ p ∈ Nat.primesLE ⌊z⌋₊, 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ z := by
    intro p hp
    have := Nat.mem_primesLE.mp hp
    exact ⟨by exact_mod_cast this.2.two_le,
      (Nat.cast_le.mpr this.1).trans (Nat.floor_le (by linarith))⟩
  have hneg : -δ = 1 / Real.log z - 1 := by rw [hδ, hη]; ring
  have hle_a : ∀ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ) ^ (-δ) ≤ a := by
    intro p hp
    obtain ⟨h2, -⟩ := hprime p hp
    calc (p : ℝ) ^ (-δ) ≤ (2 : ℝ) ^ (-δ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-δ₀) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hprod : ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ) ^ (-δ))⁻¹ ≤
      Real.exp (∑ p ∈ Nat.primesLE ⌊z⌋₊, ((p : ℝ) ^ (-δ) + K * ((p : ℝ) ^ (-δ)) ^ 2)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro p hp
      have : 0 < 1 - (p : ℝ) ^ (-δ) := by linarith [hle_a p hp]
      positivity
    · intro p hp
      set u := (p : ℝ) ^ (-δ) with hu_def
      have hu0 : 0 < u := by have := (hprime p hp).1; positivity
      have hua : u ≤ a := hle_a p hp
      have h1u : 0 < 1 - u := by linarith
      have hexp := Real.add_one_le_exp (u / (1 - u))
      have heq : u / (1 - u) + 1 = (1 - u)⁻¹ := by field_simp; ring
      have hle : u / (1 - u) ≤ u + K * u ^ 2 := by
        have hK' : (1 - u)⁻¹ ≤ K := by
          rw [hK]; exact inv_anti₀ (by linarith) (by linarith)
        have : u / (1 - u) = u + u ^ 2 * (1 - u)⁻¹ := by field_simp; ring
        rw [this]
        nlinarith [sq_nonneg u]
      rw [← heq]
      exact hexp.trans (Real.exp_le_exp.mpr hle)
  have hsum1 : ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ) ^ (-δ) ≤
      ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ)⁻¹ +
        E * η * ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h2, hpz⟩ := hprime p hp
    rw [hneg]
    exact Real.rpow_inv_log_sub_one_le (by linarith) hpz hlz0
  have hsum2 : ∑ p ∈ Nat.primesLE ⌊z⌋₊, K * ((p : ℝ) ^ (-δ)) ^ 2 ≤ K * E ^ 2 * M := by
    rw [← Finset.mul_sum, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hK0.le
    calc ∑ p ∈ Nat.primesLE ⌊z⌋₊, ((p : ℝ) ^ (-δ)) ^ 2
          ≤ ∑ p ∈ Nat.primesLE ⌊z⌋₊, E ^ 2 * ((p : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨h2, hpz⟩ := hprime p hp
          have hp0 : (0 : ℝ) < p := by linarith
          have hu : (p : ℝ) ^ (-δ) ≤ E * (p : ℝ)⁻¹ := by
            rw [hneg, Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [Real.rpow_def_of_pos hp0, hE]
            refine Real.exp_le_exp.mpr ?_
            rw [mul_one_div, div_le_one hlz0]
            exact Real.log_le_log hp0 hpz
          calc ((p : ℝ) ^ (-δ)) ^ 2 ≤ (E * (p : ℝ)⁻¹) ^ 2 := by
                gcongr
            _ = E ^ 2 * ((p : ℝ) ^ 2)⁻¹ := by ring
      _ = E ^ 2 * ∑ p ∈ Nat.primesLE ⌊z⌋₊, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ E ^ 2 * M := by gcongr; exact hM _
  have hmert : ∑ p ∈ Nat.primesLE ⌊z⌋₊, (p : ℝ)⁻¹ ≤ Real.log (Real.log z) + C₁ :=
    hMert z (by linarith)
  have hlp : E * η * ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / (p : ℝ) ≤ E + E * B := by
    have h := Chebyshev.sum_primesLE_log_div_le ⌊z⌋₊ hz1
    have hfl : Real.log ⌊z⌋₊ ≤ Real.log z :=
      Real.log_le_log (by exact_mod_cast hz1) (Nat.floor_le (by linarith))
    have : η * ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / (p : ℝ) ≤ 1 + B := by
      rw [hη, one_div_mul_eq_div, div_le_iff₀ hlz0]; nlinarith
    calc E * η * ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / (p : ℝ)
        = E * (η * ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / (p : ℝ)) := by ring
      _ ≤ E * (1 + B) := by gcongr
      _ = E + E * B := by ring
  have hS : ∑ p ∈ Nat.primesLE ⌊z⌋₊, ((p : ℝ) ^ (-δ) + K * ((p : ℝ) ^ (-δ)) ^ 2) ≤
      Real.log (Real.log z) + (C₁ + E + E * B + K * E ^ 2 * M) := by
    rw [Finset.sum_add_distrib]; linarith
  have hexp : Real.exp (∑ p ∈ Nat.primesLE ⌊z⌋₊, ((p : ℝ) ^ (-δ) + K * ((p : ℝ) ^ (-δ)) ^ 2)) ≤
      Real.log z * Real.exp (C₁ + E + E * B + K * E ^ 2 * M) := by
    calc _ ≤ Real.exp (Real.log (Real.log z) + (C₁ + E + E * B + K * E ^ 2 * M)) :=
          Real.exp_le_exp.mpr hS
      _ = _ := by rw [Real.exp_add, Real.exp_log hlz0]
  calc ((⌊x⌋₊.smoothNumbersUpTo (⌊z⌋₊ + 1)).card : ℝ)
      ≤ x ^ δ * ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ) ^ (-δ))⁻¹ := h5
    _ ≤ x ^ δ * (Real.log z * Real.exp (C₁ + E + E * B + K * E ^ 2 * M)) := by
        gcongr
        exact hprod.trans hexp
    _ = _ := by rw [hxδ]; ring

/-! ### Rankin's bound for weighted sifted divisors -/

section Weighted

variable (P : ℕ → Prop) [DecidablePred P] (ω : ℕ → ℝ) (κ B : ℝ)

/-- A sieve-dimension hypothesis `∑_{p ≤ z, P p} ω(p) log p / p ≤ κ log z + B` with `ω ≥ 0`
forces `κ ≥ 0`. -/
private lemma kappa_nonneg (hω0 : ∀ p, 0 ≤ ω p)
    (hκ : ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ (primesLE ⌊z⌋₊).filter P, ω p * Real.log p / p ≤ κ * Real.log z + B) :
    0 ≤ κ := by
  by_contra hneg
  replace hneg := not_le.mp hneg
  have hpos : 0 < -κ := by linarith
  set z₀ := Real.exp ((|B| + 1) / (-κ)) + 2 with hz₀
  have h2 : 2 ≤ z₀ := by have := Real.exp_pos ((|B| + 1) / (-κ)); linarith
  have hlog : (|B| + 1) / (-κ) ≤ Real.log z₀ := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have hsum := hκ z₀ h2
  have hnn : 0 ≤ ∑ p ∈ (primesLE ⌊z₀⌋₊).filter P, ω p * Real.log p / p :=
    Finset.sum_nonneg fun p _ => by
      have := hω0 p; have := Real.log_natCast_nonneg p; positivity
  have : κ * Real.log z₀ ≤ -(|B| + 1) := by
    rw [div_le_iff₀ hpos] at hlog; linarith
  linarith [le_abs_self B]

/-- Partial summation turns the dimension hypothesis into the Mertens-type bound
`∑_{p ≤ z, P p} ω(p)/p ≤ κ log log z + B₁`. -/
private lemma sum_div_le_log_log (hκ : ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ (primesLE ⌊z⌋₊).filter P, ω p * Real.log p / p ≤ κ * Real.log z + B)
    (hκ0 : 0 ≤ κ) :
    ∀ z : ℝ, 3 ≤ z → ∑ p ∈ (primesLE ⌊z⌋₊).filter P, ω p / p ≤
      κ * Real.log (Real.log z) + (κ - κ * Real.log (Real.log 2) + B / Real.log 2) := by
  set a : ℕ → ℝ := fun n => if n.Prime ∧ P n then ω n * Real.log n / n else 0 with ha
  have hA : ∀ N : ℕ, ∑ p ∈ (primesLE N).filter P, ω p * Real.log p / p =
      ∑ n ∈ Finset.range (N + 1), a n := fun N => by
    rw [primesLE_eq_filter_range, Finset.filter_filter, Finset.sum_filter]
  have hS : ∀ N : ℕ, ∑ p ∈ (primesLE N).filter P, ω p / p =
      ∑ n ∈ Finset.range (N + 1), a n / Real.log n := fun N => by
    rw [primesLE_eq_filter_range, Finset.filter_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha]
    split_ifs with h
    · have : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.1.one_lt)
      field_simp
    · simp
  have hAN : ∀ N : ℕ, 2 ≤ N → ∑ n ∈ Finset.range (N + 1), a n ≤ κ * Real.log N + B := by
    intro N hN
    simpa [← hA, Nat.floor_natCast] using hκ N (by exact_mod_cast hN)
  have hAbel : ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range (N + 1), a n / Real.log n -
          (∑ n ∈ Finset.range (N + 1), a n) / Real.log N ≤
        κ * (Real.log (Real.log N) - Real.log (Real.log 2)) +
          B * (1 / Real.log 2 - 1 / Real.log N) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp [Finset.sum_range_succ, ha]
    | succ N hN ih =>
      rw [Finset.sum_range_succ (fun n => a n / Real.log n), Finset.sum_range_succ (fun n => a n)]
      have hx : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hxy : Real.log N < Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_lt_log (by positivity) (by push_cast; linarith)
      have hAN := hAN N hN
      have hli : 1 - Real.log N / Real.log ((N + 1 : ℕ) : ℝ) ≤
          Real.log (Real.log ((N + 1 : ℕ) : ℝ)) - Real.log (Real.log N) := by
        have := Real.one_sub_inv_le_log_of_pos
          (x := Real.log ((N + 1 : ℕ) : ℝ) / Real.log N) (_root_.div_pos (by linarith) hx)
        rwa [Real.log_div (by linarith) hx.ne', inv_div] at this
      generalize Real.log ((N + 1 : ℕ) : ℝ) = y at hxy hli ⊢
      generalize Real.log N = x at hx hxy hli hAN ih ⊢
      generalize ∑ n ∈ Finset.range (N + 1), a n = A at hAN ih ⊢
      generalize ∑ n ∈ Finset.range (N + 1), a n / Real.log n = S at ih ⊢
      generalize a (N + 1) = c
      have hy : 0 < y := by linarith
      have h1 : A / x - A / y ≤ κ * (1 - x / y) + B * (1 / x - 1 / y) := by
        have e1 : A / x - A / y = A * (1 / x - 1 / y) := by ring
        have e2 : κ * (1 - x / y) + B * (1 / x - 1 / y) = (κ * x + B) * (1 / x - 1 / y) := by
          field_simp
        rw [e1, e2]
        refine mul_le_mul_of_nonneg_right hAN ?_
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hx hxy.le
      have h2 := mul_le_mul_of_nonneg_left hli hκ0
      have e3 : S + c / y - (A + c) / y = S - A / y := by ring
      rw [e3]
      linarith
  intro z hz
  set N := ⌊z⌋₊ with hNdef
  have hN : 2 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNz : Real.log N ≤ Real.log z := Real.log_le_log hN0 (Nat.floor_le (by linarith))
  have hll : Real.log (Real.log N) ≤ Real.log (Real.log z) := Real.log_le_log hx hNz
  have hab := hAbel N hN
  have hAN := hAN N hN
  have hdiv : (∑ n ∈ Finset.range (N + 1), a n) / Real.log N ≤ κ + B / Real.log N := by
    rw [div_le_iff₀ hx]
    have : (κ + B / Real.log N) * Real.log N = κ * Real.log N + B := by field_simp
    linarith
  rw [hS]
  have := mul_le_mul_of_nonneg_left hll hκ0
  have e : B * (1 / Real.log 2 - 1 / Real.log N) = B / Real.log 2 - B / Real.log N := by ring
  linarith

/-- **Rankin's bound.** Let `ω ≥ 0` satisfy the sieve-dimension condition
`∑_{p ≤ z, P p} ω(p) log p / p ≤ κ log z + B` for `z ≥ 2`. Then, writing
`ω(d) = ∏_{p ∣ d} ω(p)` and `P(z) = ∏_{p ≤ z, P p} p`,
`∑_{d ∣ P(z), d ≤ t} ω(d) ≤ C t (log z)^κ exp(-log t / log z)` for `t ≥ 1`, `z ≥ 3`. -/
theorem sum_divisors_siftingPrimorial_le (hω0 : ∀ p, 0 ≤ ω p)
    (hκ : ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ (primesLE ⌊z⌋₊).filter P, ω p * Real.log p / p ≤ κ * Real.log z + B) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ z : ℝ, 3 ≤ z →
      ∑ d ∈ (siftingPrimorial P ⌊z⌋₊).divisors with ((d : ℕ) : ℝ) ≤ t, ∏ p ∈ d.primeFactors, ω p ≤
        C * t * Real.log z ^ κ * Real.exp (-(Real.log t / Real.log z)) := by
  have hκ0 : 0 ≤ κ := kappa_nonneg P ω κ B hω0 hκ
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  set B1 := κ - κ * Real.log (Real.log 2) + B / Real.log 2 with hB1
  have hMert := sum_div_le_log_log P ω κ B hκ hκ0
  set E := Real.exp 1 with hE
  have hE0 : 0 < E := Real.exp_pos 1
  refine ⟨Real.exp (B1 + E * (κ + |B|)), ?_⟩
  intro t ht z hz
  have hlz : 1 < Real.log z := hlog3.trans_le (Real.log_le_log (by norm_num) hz)
  have hlz0 : 0 < Real.log z := by linarith
  set η := 1 / Real.log z with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by rw [hη, div_lt_one hlz0]; exact hlz
  set δ := 1 - η with hδ
  have hδpos : 0 < δ := by linarith
  have ht0 : 0 < t := by linarith
  have htδ : t ^ δ = t * Real.exp (-(Real.log t / Real.log z)) := by
    rw [Real.rpow_def_of_pos ht0, hδ, hη]
    conv_rhs => rw [← Real.exp_log ht0]
    rw [← Real.exp_add, Real.log_exp]
    congr 1; ring
  set S := (primesLE ⌊z⌋₊).filter P with hSdef
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => prime_of_mem_primesLE_filter hp
  have hsq : Squarefree (siftingPrimorial P ⌊z⌋₊) := squarefree_siftingPrimorial P _
  have hpf : (siftingPrimorial P ⌊z⌋₊).primeFactors = S := primeFactors_siftingPrimorial P _
  set g : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors (fun p => ω p * (p : ℝ) ^ (-δ)) with hg
  have heuler := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (fun p => ω p * (p : ℝ) ^ (-δ))).prodPrimeFactors_one_add_of_squarefree hsq
  have hgd : ∀ d : ℕ, d ≠ 0 → g d = ∏ p ∈ d.primeFactors, ω p * (p : ℝ) ^ (-δ) :=
    fun d hd => ArithmeticFunction.prodPrimeFactors_apply hd
  have hgp : ∀ p : ℕ, p.Prime → g p = ω p * (p : ℝ) ^ (-δ) := fun p hp => by
    rw [hgd p hp.ne_zero, hp.primeFactors, Finset.prod_singleton]
  have hg0 : ∀ d : ℕ, 0 ≤ g d := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [hgd d hd]
      exact Finset.prod_nonneg fun p _ => mul_nonneg (hω0 p) (by positivity)
  -- Rankin's trick
  have step1 : ∑ d ∈ (siftingPrimorial P ⌊z⌋₊).divisors with ((d : ℕ) : ℝ) ≤ t,
      ∏ p ∈ d.primeFactors, ω p ≤ t ^ δ * ∑ d ∈ (siftingPrimorial P ⌊z⌋₊).divisors, g d := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ d ∈ (siftingPrimorial P ⌊z⌋₊).divisors with ((d : ℕ) : ℝ) ≤ t, t ^ δ * g d := by
          refine Finset.sum_le_sum fun d hd => ?_
          simp only [Finset.mem_filter, Nat.mem_divisors] at hd
          obtain ⟨⟨hdvd, -⟩, hdt⟩ := hd
          have hdsq : Squarefree d := hsq.squarefree_of_dvd hdvd
          have hd0 : d ≠ 0 := hdsq.ne_zero
          rw [hgd d hd0, Finset.prod_mul_distrib,
            Real.finsetProd_rpow _ _ (fun p _ => by positivity),
            ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hdsq,
            Real.rpow_neg (by positivity)]
          have hW : 0 ≤ ∏ p ∈ d.primeFactors, ω p := Finset.prod_nonneg fun p _ => hω0 p
          have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
          have hdδ : (0 : ℝ) < (d : ℝ) ^ δ := by positivity
          have hdt' : (d : ℝ) ^ δ ≤ t ^ δ := Real.rpow_le_rpow hdpos.le hdt hδpos.le
          rw [show t ^ δ * ((∏ p ∈ d.primeFactors, ω p) * ((d : ℝ) ^ δ)⁻¹) =
            (∏ p ∈ d.primeFactors, ω p) * (t ^ δ / (d : ℝ) ^ δ) by ring]
          exact le_mul_of_one_le_right hW ((one_le_div hdδ).mpr hdt')
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => mul_nonneg (by positivity) (hg0 d))
  -- Euler product and `1 + y ≤ e^y`
  have step2 : ∑ d ∈ (siftingPrimorial P ⌊z⌋₊).divisors, g d ≤
      Real.exp (∑ p ∈ S, ω p * (p : ℝ) ^ (-δ)) := by
    rw [← heuler, hpf]
    calc ∏ p ∈ S, (1 + g p) = ∏ p ∈ S, (1 + ω p * (p : ℝ) ^ (-δ)) :=
          Finset.prod_congr rfl fun p hp => by rw [hgp p (hSprime p hp)]
      _ ≤ _ := Real.prod_one_add_le_exp_sum S fun i => mul_nonneg (hω0 i) (by positivity)
  have hneg : -δ = 1 / Real.log z - 1 := by rw [hδ, hη]; ring
  have step3 : ∑ p ∈ S, ω p * (p : ℝ) ^ (-δ) ≤
      ∑ p ∈ S, ω p / p + E * η * ∑ p ∈ S, ω p * Real.log p / p := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := hSprime p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hpz : (p : ℝ) ≤ z := by
      have := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      exact (Nat.cast_le.mpr this.1).trans (Nat.floor_le (by linarith))
    have h := Real.rpow_inv_log_sub_one_le hp1 hpz hlz0
    rw [hneg]
    calc ω p * (p : ℝ) ^ (1 / Real.log z - 1)
        ≤ ω p * ((p : ℝ)⁻¹ + E * η * (Real.log p / p)) :=
          mul_le_mul_of_nonneg_left h (hω0 p)
      _ = ω p / p + E * η * (ω p * Real.log p / p) := by ring
  have hlp : E * η * ∑ p ∈ S, ω p * Real.log p / p ≤ E * (κ + |B|) := by
    have h := hκ z (by linarith)
    have hB' : B / Real.log z ≤ |B| := by
      rw [div_le_iff₀ hlz0]; nlinarith [abs_nonneg B, le_abs_self B]
    have : η * ∑ p ∈ S, ω p * Real.log p / p ≤ κ + |B| := by
      calc η * ∑ p ∈ S, ω p * Real.log p / p ≤ η * (κ * Real.log z + B) :=
            mul_le_mul_of_nonneg_left h hη0.le
        _ = κ + B / Real.log z := by rw [hη]; field_simp
        _ ≤ κ + |B| := by linarith
    calc E * η * ∑ p ∈ S, ω p * Real.log p / p
        = E * (η * ∑ p ∈ S, ω p * Real.log p / p) := by ring
      _ ≤ E * (κ + |B|) := by gcongr
  have hm := hMert z hz
  have hX : ∑ p ∈ S, ω p * (p : ℝ) ^ (-δ) ≤
      κ * Real.log (Real.log z) + (B1 + E * (κ + |B|)) := by
    linarith
  have hexp : Real.exp (∑ p ∈ S, ω p * (p : ℝ) ^ (-δ)) ≤
      Real.log z ^ κ * Real.exp (B1 + E * (κ + |B|)) := by
    calc _ ≤ Real.exp (κ * Real.log (Real.log z) + (B1 + E * (κ + |B|))) :=
          Real.exp_le_exp.mpr hX
      _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hlz0, mul_comm κ]
  calc _ ≤ t ^ δ * ∑ d ∈ (siftingPrimorial P ⌊z⌋₊).divisors, g d := step1
    _ ≤ t ^ δ * (Real.log z ^ κ * Real.exp (B1 + E * (κ + |B|))) := by
        gcongr
        exact step2.trans hexp
    _ = _ := by rw [htδ]; ring

/-- The tail of the sifted divisor sum: under the hypotheses of
`Nat.sum_divisors_siftingPrimorial_le`, for every `c > 0`,
`∑_{d ∣ P(z), d > c x} ω(d) / d ≤ K (log z)^{κ+1} exp(-log x / log z)` for `x ≥ 1`, `z ≥ 3`. -/
theorem sum_divisors_siftingPrimorial_div_le (c : ℝ) (hω0 : ∀ p, 0 ≤ ω p)
    (hκ : ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ (primesLE ⌊z⌋₊).filter P, ω p * Real.log p / p ≤ κ * Real.log z + B)
    (hc : 0 < c) :
    ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ z : ℝ, 3 ≤ z →
      ∑ d ∈ (siftingPrimorial P ⌊z⌋₊).divisors with c * x < ((d : ℕ) : ℝ),
          (∏ p ∈ d.primeFactors, ω p) / (d : ℝ) ≤
        K * Real.log z ^ (κ + 1) * Real.exp (-(Real.log x / Real.log z)) := by
  obtain ⟨C, hC⟩ := sum_divisors_siftingPrimorial_le P ω κ B hω0 hκ
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * C' / Real.log 2 * Real.exp |Real.log c|, ?_⟩
  intro x hx z hz
  set D := (siftingPrimorial P ⌊z⌋₊).divisors with hD
  set W : ℕ → ℝ := fun d => ∏ p ∈ d.primeFactors, ω p with hW
  have hW0 : ∀ d, 0 ≤ W d := fun d => Finset.prod_nonneg fun p _ => hω0 p
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  set L := Real.log z with hL
  have hL1 : 1 < L := hlog3.trans_le (Real.log_le_log (by norm_num) hz)
  have hL0 : 0 < L := by linarith
  set y := c * x with hy
  have hy0 : 0 < y := by positivity
  set a := Real.exp (-(Real.log 2 / L)) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have hu0 : 0 < Real.log 2 / L := _root_.div_pos hlog2 hL0
  have ha1 : a < 1 := by rw [ha, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  set M := 2 * C' * L ^ κ * Real.exp (-(Real.log y / L)) with hM
  have hD1 : ∀ d ∈ D, (1 : ℝ) ≤ d := fun d hd => by
    have := Nat.pos_of_mem_divisors hd
    exact_mod_cast this
  -- dyadic blocks
  have hblock : ∀ k : ℕ,
      ∑ d ∈ D with 2 ^ k * y < ((d : ℕ) : ℝ) ∧ ((d : ℕ) : ℝ) ≤ 2 ^ (k + 1) * y, W d / d ≤
        M * a ^ (k + 1) := by
    intro k
    have hk0 : 0 < (2 : ℝ) ^ k * y := by positivity
    set t := (2 : ℝ) ^ (k + 1) * y with ht
    by_cases ht1 : 1 ≤ t
    · calc ∑ d ∈ D with 2 ^ k * y < ((d : ℕ) : ℝ) ∧ ((d : ℕ) : ℝ) ≤ t, W d / d
          ≤ ∑ d ∈ D with 2 ^ k * y < ((d : ℕ) : ℝ) ∧ ((d : ℕ) : ℝ) ≤ t, W d / (2 ^ k * y) := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hd' := (Finset.mem_filter.mp hd).2.1
            exact div_le_div_of_nonneg_left (hW0 d) hk0 hd'.le
        _ ≤ ∑ d ∈ D with ((d : ℕ) : ℝ) ≤ t, W d / (2 ^ k * y) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) ?_
            · simp only [Finset.mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.2⟩
            · intro d _ _; exact div_nonneg (hW0 d) hk0.le
        _ = (∑ d ∈ D with ((d : ℕ) : ℝ) ≤ t, W d) / (2 ^ k * y) := by rw [Finset.sum_div]
        _ ≤ (C' * t * L ^ κ * Real.exp (-(Real.log t / L))) / (2 ^ k * y) := by
            gcongr
            refine (hC t ht1 z hz).trans ?_
            gcongr
            exact le_max_left _ _
        _ = M * a ^ (k + 1) := by
            have hlt : Real.log t = (k + 1 : ℕ) * Real.log 2 + Real.log y := by
              rw [ht, Real.log_mul (by positivity) hy0.ne', Real.log_pow]
            rw [hM, ha, ← Real.exp_nat_mul, hlt]
            rw [show -(((k + 1 : ℕ) * Real.log 2 + Real.log y) / L) =
              -(Real.log y / L) + (k + 1 : ℕ) * -(Real.log 2 / L) by ring, Real.exp_add, ht,
              pow_succ]
            field_simp
    · have : (D.filter fun d : ℕ => 2 ^ k * y < (d : ℝ) ∧ (d : ℝ) ≤ t) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun d hd h => ?_
        have := hD1 d hd
        linarith [h.2]
      rw [this, Finset.sum_empty]
      positivity
  have hcum : ∀ k : ℕ,
      ∑ d ∈ D with y < ((d : ℕ) : ℝ) ∧ ((d : ℕ) : ℝ) ≤ 2 ^ k * y, W d / d ≤
        M * ∑ j ∈ Finset.range k, a ^ (j + 1) := by
    intro k
    induction k with
    | zero =>
      have : (D.filter fun d : ℕ => y < (d : ℝ) ∧ (d : ℝ) ≤ 2 ^ 0 * y) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun d _ h => ?_
        simp only [pow_zero, one_mul] at h
        linarith [h.1, h.2]
      rw [this, Finset.sum_empty]; simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add]
      refine le_trans ?_ (_root_.add_le_add ih (hblock k))
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun d _ => ?_
      have h2 : (2 : ℝ) ^ k * y ≤ 2 ^ (k + 1) * y := by
        rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
      have h1 : y ≤ 2 ^ k * y := le_mul_of_one_le_left hy0.le (one_le_pow₀ (by norm_num))
      have hnn : 0 ≤ W d / d := div_nonneg (hW0 d) (Nat.cast_nonneg d)
      split_ifs with c1 c2 <;>
        first
        | linarith
        | exact absurd (⟨lt_of_not_ge fun h => c2 ⟨c1.1, h⟩, c1.2⟩ :
            2 ^ k * y < (d : ℝ) ∧ (d : ℝ) ≤ 2 ^ (k + 1) * y) (by assumption)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((siftingPrimorial P ⌊z⌋₊ : ℝ) / y)
    (by norm_num : (1 : ℝ) < 2)
  have htail : ∑ d ∈ D with c * x < ((d : ℕ) : ℝ), W d / d =
      ∑ d ∈ D with y < ((d : ℕ) : ℝ) ∧ ((d : ℕ) : ℝ) ≤ 2 ^ k * y, W d / d := by
    refine Finset.sum_congr (Finset.filter_congr fun d hd => ?_) fun _ _ => rfl
    have hdle : (d : ℝ) ≤ siftingPrimorial P ⌊z⌋₊ := by
      exact_mod_cast Nat.divisor_le hd
    have : (siftingPrimorial P ⌊z⌋₊ : ℝ) ≤ 2 ^ k * y := by
      rw [div_lt_iff₀ hy0] at hk; linarith
    constructor
    · intro h; exact ⟨h, by linarith⟩
    · intro h; exact h.1
  have hgeom : ∑ j ∈ Finset.range k, a ^ (j + 1) ≤ 1 / (1 - a) := by
    calc ∑ j ∈ Finset.range k, a ^ (j + 1) ≤ ∑ j ∈ Finset.range k, a ^ j :=
          Finset.sum_le_sum fun j _ => pow_le_pow_of_le_one ha0.le ha1.le (by omega)
      _ = (1 - a ^ k) / (1 - a) := by
          rw [geom_sum_eq ha1.ne k, ← neg_div_neg_eq, neg_sub, neg_sub]
      _ ≤ 1 / (1 - a) := by
          have : 0 ≤ a ^ k := by positivity
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hinv : 1 / (1 - a) ≤ 2 * L / Real.log 2 := by
    set u := Real.log 2 / L with hu
    have hu1 : u < 1 := by
      rw [hu, div_lt_one hL0]
      have := Real.log_two_lt_d9; linarith
    have h1 := Real.add_one_le_exp u
    have h3 : a * Real.exp u = 1 := by rw [ha, ← Real.exp_add]; simp
    have hau : a * (1 + u) ≤ 1 := by nlinarith
    have h1a : u / 2 ≤ 1 - a := by nlinarith
    have : 2 * L / Real.log 2 = 1 / (u / 2) := by rw [hu]; field_simp
    rw [this]
    exact one_div_le_one_div_of_le (by positivity) h1a
  have hexp : Real.exp (-(Real.log y / L)) ≤
      Real.exp |Real.log c| * Real.exp (-(Real.log x / L)) := by
    rw [← Real.exp_add, Real.exp_le_exp, hy,
      Real.log_mul hc.ne' (by linarith : (0 : ℝ) < x).ne']
    have : -Real.log c / L ≤ |Real.log c| := by
      rw [div_le_iff₀ hL0]
      nlinarith [neg_le_abs (Real.log c), abs_nonneg (Real.log c)]
    have e : -((Real.log c + Real.log x) / L) = -Real.log c / L + -(Real.log x / L) := by ring
    linarith
  change ∑ d ∈ D with c * x < ((d : ℕ) : ℝ), W d / d ≤ _
  rw [htail, Real.rpow_add_one hL0.ne']
  calc _ ≤ M * ∑ j ∈ Finset.range k, a ^ (j + 1) := hcum k
    _ ≤ M * (2 * L / Real.log 2) := by
        gcongr
        exact hgeom.trans hinv
    _ = 4 * C' / Real.log 2 * (L ^ κ * L) * Real.exp (-(Real.log y / L)) := by
        rw [hM]; ring
    _ ≤ _ := by
        calc 4 * C' / Real.log 2 * (L ^ κ * L) * Real.exp (-(Real.log y / L))
            ≤ 4 * C' / Real.log 2 * (L ^ κ * L) *
                (Real.exp |Real.log c| * Real.exp (-(Real.log x / L))) := by gcongr
          _ = _ := by ring

end Weighted

end Nat
