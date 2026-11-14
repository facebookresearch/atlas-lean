/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.NumberTheory.LSeries.RamanujanSigma

/-!
# The average of `d(n²) / φ(n)`

The function `n ↦ d(n²) / φ(n)` is multiplicative and agrees with `n ↦ d(n²) / n · ∏ (1 - 1/p)⁻¹`;
it factors as `H * (1/n) * (d(n)/n)` with `H` supported on cube-full numbers, `H(p) = 0`, and
`∑ |H(n)| n^{1/4} < ∞`. Since `∑_{n ≤ x} (1/n * d(n)/n)(n) = (log x)³/6 + O((log x)²)`, this gives

`∑_{n ≤ x} d(n²) / φ(n) = c (log x)³ + O((log x)²)` with `c = (∑ H) / 6 > 0`.

## Main statements

* `ArithmeticFunction.abs_sum_divisors_div_sub_le`: `∑_{n ≤ u} d(n)/n = (log u)²/2 + O(1 + log u)`.
* `ArithmeticFunction.exists_abs_sum_sigma_zero_sq_div_totient_sub_le`:
  `∑_{n ≤ x} d(n²)/φ(n) = c (log x)³ + O((log x)²)` for some `c > 0`.
-/

@[expose] public section

open Finset

namespace ArithmeticFunction

/-- `|∑_{a ≤ y} (log y - log a)^{k+1} / a - (log y)^{k+2} / (k + 2)| ≤ (log y)^{k+1} + 1` for
`y ≥ 1`, by comparison with `∫_1^y (log y - log t)^{k+1} / t dt`. -/
private theorem abs_sum_log_sub_pow_div_sub_le (k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    |∑ a ∈ Icc 1 ⌊y⌋₊, (Real.log y - Real.log a) ^ (k + 1) / a -
        Real.log y ^ (k + 2) / (k + 2)| ≤ Real.log y ^ (k + 1) + 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊y⌋₊ = n + 1 :=
    ⟨⌊y⌋₊ - 1, by have := Nat.one_le_floor_iff y |>.2 hy; omega⟩
  have hNy : ((n + 1 : ℕ) : ℝ) ≤ y := hn ▸ Nat.floor_le (by linarith)
  have hyN : y < ((n + 1 : ℕ) : ℝ) + 1 := hn ▸ Nat.lt_floor_add_one y
  push_cast at hNy hyN
  have hk2 : (0 : ℝ) < k + 2 := by positivity
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun t => (Real.log y - Real.log t) ^ (k + 1) / t :=
    ⟨_, rfl⟩
  have hanti : AntitoneOn φ (Set.Icc 1 (1 + (n : ℝ))) := by
    intro s hs t ht hst
    simp only [Set.mem_Icc] at hs ht
    simp only [hφ]
    have hs0 : 0 < s := by linarith
    have h1 : 0 ≤ Real.log y - Real.log t := by
      have := Real.log_le_log (by linarith) (show t ≤ y by linarith); linarith
    have h2 : Real.log y - Real.log t ≤ Real.log y - Real.log s := by
      have := Real.log_le_log hs0 hst; linarith
    exact div_le_div₀ (pow_nonneg (h1.trans h2) _) (pow_le_pow_left₀ h1 h2 _) hs0 hst
  have hint : ∫ t in (1 : ℝ)..1 + (n : ℝ), φ t
      = Real.log y ^ (k + 2) / (k + 2) - (Real.log y - Real.log (1 + n)) ^ (k + 2) / (k + 2) := by
    have hpos : ∀ t ∈ Set.uIcc (1 : ℝ) (1 + n), 0 < t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at ht
      linarith
    have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) (1 + n),
        HasDerivAt (fun t : ℝ => -(Real.log y - Real.log t) ^ (k + 2) / (k + 2)) (φ t) t := by
      intro t ht
      have ht0 := hpos t ht
      have h1 := (((Real.hasDerivAt_log ht0.ne').const_sub (Real.log y)).pow (k + 2)).neg.div_const
        ((k : ℝ) + 2)
      refine h1.congr_deriv ?_
      rw [hφ]
      field_simp
      push_cast
      ring
    have hcont : ContinuousOn φ (Set.uIcc (1 : ℝ) (1 + n)) := by
      rw [hφ]
      refine ContinuousOn.div (ContinuousOn.pow (continuousOn_const.sub
        (Real.continuousOn_log.mono fun t ht => (hpos t ht).ne')) _) continuousOn_id
        fun t ht => (hpos t ht).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    simp only [Real.log_one]
    ring
  have hsum : ∑ a ∈ Icc 1 ⌊y⌋₊, (Real.log y - Real.log a) ^ (k + 1) / a
      = ∑ i ∈ Finset.range (n + 1), φ (1 + i) := by
    rw [hn, hφ, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  have hup := hanti.sum_le_integral
  have hlow := hanti.integral_le_sum
  rw [hint] at hup hlow
  rw [hsum]
  have hφ0 : ∀ i ∈ Finset.range (n + 1), 0 ≤ φ (1 + i) := fun i hi => by
    rw [hφ]
    have h1 : 0 ≤ Real.log y - Real.log (1 + (i : ℝ)) := by
      have hi' := Finset.mem_range.1 hi
      have : (1 + (i : ℝ)) ≤ y := by
        have : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 hi'
        linarith
      have := Real.log_le_log (by positivity) this
      linarith
    positivity
  have hlast : 0 ≤ φ (1 + n) := hφ0 n (by simp)
  have hfirst : φ (1 + ((0 : ℕ) : ℝ)) = Real.log y ^ (k + 1) := by simp [hφ]
  have hA := Finset.sum_range_succ (fun i : ℕ => φ (1 + i)) n
  have hB := Finset.sum_range_succ' (fun i : ℕ => φ (1 + i)) n
  simp only [Nat.cast_zero, add_zero] at hA hB hfirst
  rw [hfirst] at hB
  have hgap0 : 0 ≤ Real.log y - Real.log (1 + n) := by
    have := Real.log_le_log (by positivity) (show 1 + (n : ℝ) ≤ y by linarith only [hNy])
    linarith only [this]
  have hgap1 : Real.log y - Real.log (1 + n) ≤ 1 := by
    have h2 : y ≤ 2 * (1 + n) := by linarith only [hyN, hNy]
    have h3 := Real.log_le_log (by linarith only [hy]) h2
    rw [Real.log_mul (by norm_num) (by positivity)] at h3
    have h4 := Real.log_two_lt_d9
    linarith only [h3, h4]
  have hpow0 : 0 ≤ (Real.log y - Real.log (1 + n)) ^ (k + 2) / (k + 2) := by positivity
  have hpow1 : (Real.log y - Real.log (1 + n)) ^ (k + 2) / (k + 2) ≤ 1 := by
    rw [div_le_one hk2]
    have := pow_le_one₀ hgap0 hgap1 (n := k + 2)
    linarith
  have hLk : 0 ≤ Real.log y ^ (k + 1) := pow_nonneg (Real.log_nonneg hy) _
  rw [abs_le]
  constructor
  · linarith only [hA, hlow, hlast, hpow1, hLk]
  · linarith only [hB, hup, hpow0]

/-- The arithmetic function `n ↦ 1/n`. -/
private noncomputable def recip : ArithmeticFunction ℝ := ⟨fun n => ((n : ℝ))⁻¹, by simp⟩

private theorem recip_apply (n : ℕ) : recip n = ((n : ℝ))⁻¹ := rfl

/-- `∑_{n ≤ u} d(n)/n = (log u)² / 2 + O(1 + log u)`: precisely,
`|∑_{n ≤ u} d(n)/n - (log u)²/2| ≤ 2 (1 + log u)` for every `u ≥ 1`. -/
theorem abs_sum_divisors_div_sub_le {u : ℝ} (hu : 1 ≤ u) :
    |∑ n ∈ Icc 1 ⌊u⌋₊, (n.divisors.card : ℝ) / n - 1 / 2 * Real.log u ^ 2| ≤
      2 * (1 + Real.log u) := by
  have hu0 : 0 < u := by linarith
  have hL : 0 ≤ Real.log u := Real.log_nonneg hu
  -- `d(n)/n = (1/n * 1/n)(n)`
  have hdd : ∀ n : ℕ, (n.divisors.card : ℝ) / n = (recip * recip) n := by
    intro n
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => recip i * recip j)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have : ∀ i ∈ n.divisors, recip i * recip (n / i) = ((n : ℝ))⁻¹ := by
      intro i hi
      rw [recip_apply, recip_apply, ← mul_inv]
      congr 1
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  -- `|H(⌊y⌋) - log y| ≤ 1`
  have hH : ∀ y : ℝ, 1 ≤ y → |∑ b ∈ Icc 1 ⌊y⌋₊, ((b : ℝ))⁻¹ - Real.log y| ≤ 1 := by
    intro y hy
    have h1 := harmonic_le_one_add_log ⌊y⌋₊
    have h2 := log_add_one_le_harmonic ⌊y⌋₊
    rw [harmonic_eq_sum_Icc] at h1 h2
    push_cast at h1 h2
    have h3 : Real.log ⌊y⌋₊ ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast Nat.one_le_floor_iff y |>.2 hy)
        (Nat.floor_le (by linarith))
    have h4 : Real.log y ≤ Real.log (⌊y⌋₊ + 1) :=
      Real.log_le_log (by linarith) (Nat.lt_floor_add_one y).le
    rw [abs_le]
    constructor <;> linarith
  have hexp : ∑ n ∈ Icc 1 ⌊u⌋₊, (n.divisors.card : ℝ) / n =
      ∑ a ∈ Icc 1 ⌊u⌋₊, ((a : ℝ))⁻¹ * ∑ b ∈ Icc 1 ⌊u / a⌋₊, ((b : ℝ))⁻¹ := by
    simp_rw [hdd]
    have := sum_Ioc_mul_eq_sum_sum recip recip ⌊u⌋₊
    simp only [recip_apply] at this
    rw [show Icc 1 ⌊u⌋₊ = Ioc 0 ⌊u⌋₊ from rfl, this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.floor_div_natCast]
    rfl
  have hharm : ∑ a ∈ Icc 1 ⌊u⌋₊, ((a : ℝ))⁻¹ ≤ 1 + Real.log u := by
    have h1 := harmonic_le_one_add_log ⌊u⌋₊
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    have h2 : Real.log ⌊u⌋₊ ≤ Real.log u :=
      Real.log_le_log (by exact_mod_cast Nat.one_le_floor_iff u |>.2 hu) (Nat.floor_le hu0.le)
    linarith
  have hS := abs_sum_log_sub_pow_div_sub_le 0 hu
  simp only [zero_add, pow_one] at hS
  norm_num at hS
  have hsplit : ∑ a ∈ Icc 1 ⌊u⌋₊, ((a : ℝ))⁻¹ * ∑ b ∈ Icc 1 ⌊u / a⌋₊, ((b : ℝ))⁻¹ =
      ∑ a ∈ Icc 1 ⌊u⌋₊, (Real.log u - Real.log a) / a +
        ∑ a ∈ Icc 1 ⌊u⌋₊, ((a : ℝ))⁻¹ *
          (∑ b ∈ Icc 1 ⌊u / a⌋₊, ((b : ℝ))⁻¹ - Real.log (u / a)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
    rw [Real.log_div hu0.ne' (by positivity)]
    ring
  have herr : |∑ a ∈ Icc 1 ⌊u⌋₊, ((a : ℝ))⁻¹ *
      (∑ b ∈ Icc 1 ⌊u / a⌋₊, ((b : ℝ))⁻¹ - Real.log (u / a))| ≤ 1 + Real.log u := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hharm)
    refine Finset.sum_le_sum fun a ha => ?_
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.1 ha).1
    have hau : (a : ℝ) ≤ u := (Nat.le_floor_iff hu0.le).1 (Finset.mem_Icc.1 ha).2
    have hya : 1 ≤ u / a := by rw [le_div_iff₀ (by linarith)]; linarith
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (hH (u / a) hya)
  rw [hexp, hsplit]
  rw [abs_le] at hS herr ⊢
  constructor <;> nlinarith

/-- `∑_{m < N} g m ≤ ∏_{p < N} ∑' e, g(p^e)` for nonnegative multiplicative `g` with `g 0 = 0`. -/
private theorem sum_range_le_prod_primesBelow_tsum {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hg00 : g 0 = 0) (hg1 : g 1 = 1) (hmul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable fun e => ‖g (p ^ e)‖) (N : ℕ) :
    ∑ m ∈ Finset.range N, g m ≤ ∏ p ∈ N.primesBelow, ∑' e, g (p ^ e) := by
  obtain ⟨-, hHas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hg1 hmul hsum (Finset.range N)
  calc ∑ m ∈ Finset.range N, g m = ∑ m ∈ (Finset.range N).filter (· ≠ 0), g m := by
        refine (Finset.sum_filter_of_ne fun x _ hx => ?_).symm
        rintro rfl
        exact hx hg00
    _ = ∑ x ∈ ((Finset.range N).filter (· ≠ 0)).subtype
          (· ∈ Nat.factoredNumbers (Finset.range N)), g x := by
        refine (Finset.sum_subtype_of_mem g fun x hx => ?_).symm
        rw [Finset.mem_filter, Finset.mem_range] at hx
        rw [← Nat.smoothNumbers_eq_factoredNumbers]
        exact Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hx.2) hx.1
    _ ≤ ∏ p ∈ Finset.range N with p.Prime, ∑' e, g (p ^ e) :=
        sum_le_hasSum _ (fun i _ => hg0 i) hHas
    _ = _ := rfl

/-- Prime-power values `v p e` with `v p 0 = 1` extend to a multiplicative arithmetic function. -/
private theorem exists_isMultiplicative_of_prime_pow {R : Type*} [CommMonoidWithZero R]
    (v : ℕ → ℕ → R) (hv0 : ∀ p, v p 0 = 1) :
    ∃ F : ArithmeticFunction R,
      (∀ p e : ℕ, p.Prime → F (p ^ e) = v p e) ∧ F.IsMultiplicative := by
  classical
  refine ⟨⟨fun n => if n = 0 then 0 else n.factorization.prod v, by simp⟩, ?_, ?_⟩
  · intro p e hp
    simp only [ArithmeticFunction.coe_mk, pow_ne_zero e hp.ne_zero, ite_false,
      Nat.Prime.factorization_pow hp]
    exact Finsupp.prod_single_index (hv0 p)
  · refine ⟨by simp, fun {m n} hmn => ?_⟩
    simp only [ArithmeticFunction.coe_mk]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [ite_eq_right (Nat.mul_ne_zero hm.ne' hn.ne'), ite_eq_right hm.ne', ite_eq_right hn.ne',
      Nat.factorization_mul_of_coprime hmn]
    refine Finsupp.prod_add_index_of_disjoint ?_ v
    rw [Nat.support_factorization, Nat.support_factorization]
    exact hmn.disjoint_primeFactors

/-- **The average order of `d(n²) / φ(n)`**: there are `c > 0` and `C` with
`|∑_{n ≤ x} d(n²)/φ(n) - c (log x)³| ≤ C (log x)²` for all `x ≥ 2`. -/
theorem exists_abs_sum_sigma_zero_sq_div_totient_sub_le :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Icc 1 ⌊x⌋₊, (sigma 0 (n ^ 2) : ℝ) / (Nat.totient n : ℝ) - c * Real.log x ^ 3| ≤
        C * Real.log x ^ 2 := by
  classical
  simp_rw [sigma_zero_apply]
  have hreindex : ∀ (A B : ArithmeticFunction ℝ) (y : ℝ),
      ∑ n ∈ Icc 1 ⌊y⌋₊, (A * B) n
        = ∑ m ∈ Icc 1 ⌊y⌋₊, A m * ∑ k ∈ Icc 1 ⌊y / m⌋₊, B k := by
    intro A B y
    rw [show Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ from rfl, sum_Ioc_mul_eq_sum_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.floor_div_natCast]
    rfl
  have hT : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ u : ℝ, 1 ≤ u →
      |∑ n ∈ Icc 1 ⌊u⌋₊, (n.divisors.card : ℝ) / n - 1 / 2 * Real.log u ^ 2|
        ≤ K₁ * (1 + Real.log u) :=
    ⟨2, by norm_num, fun u hu => abs_sum_divisors_div_sub_le hu⟩
  have hsumlog : ∀ y : ℝ, 1 ≤ y →
      |∑ a ∈ Icc 1 ⌊y⌋₊, (Real.log y - Real.log a) ^ 2 / a - Real.log y ^ 3 / 3|
        ≤ Real.log y ^ 2 + 1 := by
    intro y hy
    have := abs_sum_log_sub_pow_div_sub_le 1 hy
    norm_num at this
    exact this
  have hcore : ∀ L ℓ w K Dv : ℝ, 0 ≤ ℓ → ℓ ≤ L → 1 / 2 ≤ L → 1 ≤ w → ℓ ≤ 4 * w → 0 ≤ K →
      |Dv - (L - ℓ) ^ 3 / 6| ≤ K * (1 + (L - ℓ)) ^ 2 →
        |Dv - L ^ 3 / 6| ≤ w * ((9 * K + 2) * L ^ 2) := by
    intro L ℓ w K Dv hℓ0 hℓL hL2 hw1 hℓw hK hD1
    have h1 : 0 ≤ ℓ ^ 2 * (3 * L - ℓ) := mul_nonneg (sq_nonneg ℓ) (by linarith)
    have h2 : 0 ≤ ℓ * (3 * L ^ 2 + 3 * L * (L - ℓ) + ℓ ^ 2) := by
      have : 0 ≤ L * (L - ℓ) := mul_nonneg (by linarith) (by linarith)
      exact mul_nonneg hℓ0 (add_nonneg (add_nonneg (by positivity) (by linarith)) (sq_nonneg ℓ))
    have hcube : |(L - ℓ) ^ 3 / 6 - L ^ 3 / 6| ≤ L ^ 2 * ℓ / 2 := by
      rw [abs_le]
      constructor
      · linear_combination (1 / 6 : ℝ) * h1
      · linear_combination (1 / 6 : ℝ) * h2
    have hsq : K * (1 + (L - ℓ)) ^ 2 ≤ 9 * K * L ^ 2 := by
      have h1 : (1 + (L - ℓ)) ^ 2 ≤ (3 * L) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h2 := mul_le_mul_of_nonneg_left h1 hK
      linarith only [h2]
    have e : Dv - L ^ 3 / 6 = (Dv - (L - ℓ) ^ 3 / 6) + ((L - ℓ) ^ 3 / 6 - L ^ 3 / 6) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h3 := mul_le_mul_of_nonneg_left hℓw (sq_nonneg L)
    have h4 : 9 * K * L ^ 2 ≤ 9 * K * L ^ 2 * w :=
      le_mul_of_one_le_right (by positivity) hw1
    linarith only [hD1, hcube, hsq, h3, h4]
  obtain ⟨hv, hhv⟩ : ∃ hv : ℕ → ℕ → ℝ, hv = fun (p e : ℕ) => if e = 0 then (1:ℝ)
      else if e = 1 then 3 / ((p:ℝ) * ((p:ℝ) - 1))
      else if e = 2 then -((p:ℝ) + 3) / ((p:ℝ) ^ 2 * ((p:ℝ) - 1))
      else if e = 3 then 1 / ((p:ℝ) ^ 3 * ((p:ℝ) - 1)) else 0 := ⟨_, rfl⟩
  have hv0 : ∀ p, hv p 0 = 1 := fun p => by simp [hhv]
  obtain ⟨Hf, hHf_pp, hHf_mul⟩ : ∃ Hf : ArithmeticFunction ℝ,
      (∀ p e : ℕ, p.Prime → Hf (p ^ e) = hv p e) ∧ Hf.IsMultiplicative := by
    exact exists_isMultiplicative_of_prime_pow hv hv0
  have hA0 : ∃ A₀ : ℝ, ∀ N : ℕ,
      ∑ m ∈ Finset.range N, |Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4) ≤ A₀ := by
    clear hreindex hT hsumlog hcore
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun m => |Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
    have hg0 : ∀ m, 0 ≤ g m := fun m => by rw [hg]; positivity
    have hg1 : g 1 = 1 := by simp [hg, hHf_mul.map_one]
    have hgmul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := by
      intro m n hmn
      simp only [hg]
      rw [hHf_mul.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring
    have hgpp : ∀ p e : ℕ, p.Prime → 4 ≤ e → g (p ^ e) = 0 := by
      intro p e hp he
      simp only [hg, hHf_pp p e hp, hhv]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp
    have hgsum : ∀ {p : ℕ}, p.Prime → Summable fun e => ‖g (p ^ e)‖ := by
      intro p hp
      refine summable_of_ne_finset_zero (s := Finset.range 4) fun e he => ?_
      rw [Finset.mem_range, not_lt] at he
      simp [hgpp p e hp he]
    -- the local factor
    have hfac : ∀ p : ℕ, p.Prime →
        ∑' e, g (p ^ e) ≤ 1 + 12 * (((p : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹ := by
      intro p hp
      rw [tsum_eq_sum (s := Finset.range 4) fun e he => by
        rw [Finset.mem_range, not_lt] at he; exact hgpp p e hp he]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hg, hHf_pp _ _ hp, hhv]
      norm_num
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (p : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hs4 : s ^ 4 = p := by
        rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_rpow (by linarith) (by norm_num)
      have e2 : ((p : ℝ) ^ 2) ^ ((1 : ℝ) / 4) = s ^ 2 := by
        rw [hs, Real.rpow_pow_comm (by linarith)]
      have e3 : ((p : ℝ) ^ 3) ^ ((1 : ℝ) / 4) = s ^ 3 := by
        rw [hs, Real.rpow_pow_comm (by linarith)]
      rw [← hs, e2, e3, ← hs4]
      have hs4' : 2 ≤ s ^ 4 := hs4 ▸ hp2
      have hq : 0 < s ^ 4 - 1 := by linarith
      have hs0 : 0 < s := by linarith
      rw [abs_of_pos (show (0:ℝ) < 3 / (s ^ 4 * (s ^ 4 - 1)) by positivity), abs_div,
        show |-3 + -s ^ 4| = s ^ 4 + 3 by rw [abs_of_neg (by linarith [pow_pos hs0 4])]; ring,
        abs_of_pos (show 0 < (s ^ 4) ^ 2 * (s ^ 4 - 1) by positivity), abs_of_pos hq]
      have b1 : 3 / (s ^ 4 * (s ^ 4 - 1)) * s ≤ 6 * (s ^ 6)⁻¹ := by
        rw [div_mul_eq_mul_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
        have : 0 ≤ s ^ 4 * ((s ^ 4 - 2) + s ^ 3 * (s - 1)) := by
          have := mul_nonneg (by linarith : (0:ℝ) ≤ s ^ 3) (by linarith : (0:ℝ) ≤ s - 1)
          positivity
        linear_combination 3 * this
      have b2 : ((s ^ 4) + 3) / ((s ^ 4) ^ 2 * (s ^ 4 - 1)) * s ^ 2 ≤ 5 * (s ^ 6)⁻¹ := by
        rw [div_mul_eq_mul_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ s ^ 8 * (4 * s ^ 4 - 8) := mul_nonneg (by positivity) (by linarith)
        linear_combination this
      have b3 : (s ^ 4 - 1)⁻¹ * ((s ^ 4) ^ 3)⁻¹ * s ^ 3 ≤ (s ^ 6)⁻¹ := by
        rw [← mul_inv, mul_comm, ← div_eq_mul_inv, ← one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
        have : 0 ≤ s ^ 9 * (s ^ 3 * (s ^ 4 - 1) - 1) := by
          have : 1 ≤ s ^ 3 * (s ^ 4 - 1) := one_le_mul_of_one_le_of_one_le h3 (by linarith)
          exact mul_nonneg (by positivity) (by linarith)
        linear_combination this
      linarith
    have hw : ∀ n : ℕ, ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 6 = (n : ℝ) ^ ((3 : ℝ) / 2) := by
      intro n
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
    have hZs : Summable fun n : ℕ => (((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹ := by
      simp only [hw]; exact Real.summable_nat_rpow_inv.2 (by norm_num)
    refine ⟨Real.exp (12 * ∑' n : ℕ, (((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹), fun N => ?_⟩
    have key : ∑ m ∈ Finset.range N, g m
        ≤ Real.exp (12 * ∑' n : ℕ, (((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹) := by
      calc ∑ m ∈ Finset.range N, g m
          ≤ ∏ p ∈ N.primesBelow, ∑' e, g (p ^ e) :=
            sum_range_le_prod_primesBelow_tsum hg0 (by simp [hg]) hg1 hgmul hgsum N
        _ ≤ ∏ p ∈ N.primesBelow, Real.exp (12 * (((p : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹) := by
            refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg fun e => hg0 _) fun p hp => ?_
            refine (hfac p (Nat.prime_of_mem_primesBelow hp)).trans ?_
            have := Real.add_one_le_exp (12 * (((p : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹)
            linarith
        _ = Real.exp (∑ p ∈ N.primesBelow, 12 * (((p : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹) :=
            (Real.exp_sum _ _).symm
        _ ≤ Real.exp (12 * ∑' n : ℕ, (((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 6)⁻¹) := by
            rw [Real.exp_le_exp, ← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact hZs.sum_le_tsum _ fun i _ => by positivity
    simpa only [hg] using key
  obtain ⟨A₀, hA₀⟩ := hA0
  have hA₀0 : 0 ≤ A₀ := by simpa using hA₀ 0
  -- absolute summability of `Hf`
  have hHf0 : Hf 0 = 0 := Hf.map_zero
  have hw1 : ∀ m : ℕ, |Hf m| ≤ |Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hHf0]
    · exact le_mul_of_one_le_right (abs_nonneg _)
        (Real.one_le_rpow (by exact_mod_cast hm) (by norm_num))
  have hsumabs : Summable fun m => ‖Hf m‖ := by
    refine summable_of_sum_range_le (c := A₀) (fun m => norm_nonneg _) fun N => ?_
    refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hA₀ N)
    rw [Real.norm_eq_abs]; exact hw1 m
  have hgsum : Summable fun m : ℕ => |Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4) :=
    summable_of_sum_range_le (fun m => by positivity) hA₀
  -- the Euler product gives `∑ Hf ≥ 1`
  have hHpos : 1 ≤ ∑' m, Hf m := by
    clear hreindex hT hsumlog hcore hw1 hgsum hA₀ hA₀0
    have hE := EulerProduct.eulerProduct_hasProd (f := fun m => Hf m) hHf_mul.map_one
      (fun h => hHf_mul.map_mul_of_coprime h) hsumabs hHf0
    refine ge_of_tendsto' hE fun s => ?_
    rw [← Finset.prod_const_one (s := s)]
    refine Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun p _ => ?_
    have hp := p.2
    rw [tsum_eq_sum (s := Finset.range 4) fun e he => by
      rw [Finset.mem_range, not_lt] at he
      simp only [hHf_pp _ _ hp, hhv]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hHf_pp _ _ hp, hv0]
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hp.two_le
    have hq : (0 : ℝ) < (p : ℕ) - 1 := by linarith
    have hval : hv p 1 + hv p 2 + hv p 3 = (2 * ((p : ℕ) : ℝ) - 1) / ((p : ℕ) : ℝ) ^ 3 := by
      simp only [hhv]
      norm_num
      field_simp
      ring
    have h2 : 0 ≤ (2 * ((p : ℕ) : ℝ) - 1) / ((p : ℕ) : ℝ) ^ 3 :=
      div_nonneg (by linarith) (by positivity)
    linarith
  -- the tail of `∑ Hf`
  have htail : ∀ x : ℝ, 1 ≤ x →
      |∑ m ∈ Finset.Icc 1 ⌊x⌋₊, Hf m - ∑' m, Hf m| ≤ A₀ / x ^ ((1 : ℝ) / 4) := by
    clear hreindex hT hsumlog hcore hHpos hHf_pp hhv hv0 hHf_mul hw1
    intro x hx
    obtain ⟨N, hN⟩ : ∃ N, N = ⌊x⌋₊ := ⟨_, rfl⟩
    rw [← hN]
    have hxN : x < (N : ℝ) + 1 := hN ▸ Nat.lt_floor_add_one x
    have hx4 : 0 < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
    have h1 : ∑ m ∈ Finset.Icc 1 N, Hf m = ∑ m ∈ Finset.range (N + 1), Hf m := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hHf0, zero_add,
        Finset.Ico_add_one_right_eq_Icc]
    have h2 := (hsumabs.of_norm).sum_add_tsum_nat_add (N + 1)
    rw [h1, ← h2, sub_add_cancel_left, abs_neg]
    have hs1 : Summable fun i => ‖Hf (i + (N + 1))‖ :=
      (summable_nat_add_iff (f := fun m => ‖Hf m‖) (N + 1)).2 hsumabs
    have hs2 : Summable fun i => |Hf (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
      (summable_nat_add_iff (f := fun m : ℕ => |Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4)) (N + 1)).2 hgsum
    refine (norm_tsum_le_tsum_norm hs1).trans ?_
    have hle : ∀ i : ℕ, ‖Hf (i + (N + 1))‖
        ≤ |Hf (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 4) / x ^ ((1 : ℝ) / 4) := by
      intro i
      rw [Real.norm_eq_abs, le_div_iff₀ hx4]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine Real.rpow_le_rpow (by linarith) ?_ (by norm_num)
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    refine (hs1.tsum_le_tsum hle (hs2.div_const _)).trans ?_
    rw [tsum_div_const]
    refine div_le_div_of_nonneg_right ?_ hx4.le
    refine Real.tsum_le_of_sum_range_le (fun i => by positivity) fun K => ?_
    have h3 := Finset.sum_range_add (fun m : ℕ => |Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4)) (N + 1) K
    have h4 : 0 ≤ ∑ m ∈ Finset.range (N + 1), |Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4) :=
      Finset.sum_nonneg fun m _ => by positivity
    have h5 := hA₀ (N + 1 + K)
    simp only [add_comm _ (N + 1)] at h3 ⊢
    linarith
  clear hw1 hsumabs hgsum hHf0
  obtain ⟨R, hR⟩ : ∃ R : ArithmeticFunction ℝ, ∀ n, R n = ((n : ℝ))⁻¹ :=
    ⟨⟨fun n => ((n : ℝ))⁻¹, by simp⟩, fun n => rfl⟩
  have hRm : R.IsMultiplicative := by
    refine ⟨by simp [hR], fun {m n} _ => ?_⟩
    simp only [hR]; push_cast; exact mul_inv _ _
  obtain ⟨Dd, hDd⟩ : ∃ Dd : ArithmeticFunction ℝ, ∀ n, Dd n = (n.divisors.card : ℝ) / n :=
    ⟨⟨fun n => (n.divisors.card : ℝ) / n, by simp⟩, fun n => rfl⟩
  have hDdm : Dd.IsMultiplicative := by
    refine ⟨by simp [hDd], fun {m n} hmn => ?_⟩
    simp only [hDd]; rw [Nat.Coprime.card_divisors_mul hmn]; push_cast
    exact mul_div_mul_comm _ _ _ _
  have hF0 : ((0 ^ 2 : ℕ).divisors.card : ℝ) / (Nat.totient 0 : ℝ) = 0 := by simp
  obtain ⟨F, hF⟩ : ∃ F : ArithmeticFunction ℝ, ∀ n,
      F n = ((n ^ 2).divisors.card : ℝ) / (Nat.totient n : ℝ) :=
    ⟨⟨fun n => ((n ^ 2).divisors.card : ℝ) / (Nat.totient n : ℝ), hF0⟩, fun n => rfl⟩
  have hFm : F.IsMultiplicative := by
    refine ⟨by simp [hF], fun {m n} hmn => ?_⟩
    simp only [hF]
    rw [mul_pow, Nat.Coprime.card_divisors_mul (Nat.Coprime.pow 2 2 hmn), Nat.totient_mul hmn,
      Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]
  -- values at prime powers
  have hGpp : ∀ p i : ℕ, p.Prime →
      (R * Dd) (p ^ i) = ((i : ℝ) + 1) * ((i : ℝ) + 2) / 2 / (p : ℝ) ^ i := by
    clear hreindex hT hsumlog hcore htail hHpos hA₀ hA₀0 hF hFm hHf_pp hHf_mul hhv hv0
    intro p i hp
    rw [mul_apply_prime_pow _ _ hp]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hterm : ∀ j ∈ Finset.range (i + 1), R (p ^ j) * Dd (p ^ (i - j))
        = ((i : ℝ) - j + 1) / (p : ℝ) ^ i := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hR, hDd, ← ArithmeticFunction.sigma_zero_apply,
        ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hpow : (p : ℝ) ^ i = (p : ℝ) ^ j * (p : ℝ) ^ (i - j) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, Nat.cast_add, Nat.cast_sub (by omega : j ≤ i), Nat.cast_pow, Nat.cast_pow]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    congr 1
    clear hterm
    induction i with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have : ∀ j ∈ Finset.range (k + 1), ((k + 1 : ℕ) : ℝ) - j + 1 = ((k : ℝ) - j + 1) + 1 := by
        intro j _; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ih]
      simp
      ring
  have hFpp : ∀ p k : ℕ, p.Prime →
      F (p ^ (k + 1)) = (2 * (k : ℝ) + 3) / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
    clear hreindex hT hsumlog hcore htail hHpos hA₀ hA₀0 hFm hHf_pp hHf_mul hhv hv0 hGpp hR hDd
      hRm hDdm
    intro p k hp
    rw [hF, ← pow_mul, ← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp, Nat.totient_prime_pow hp (by omega),
      Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le]
    push_cast
    congr 1
    ring
  have hv1 : ∀ p : ℕ, hv p 1 = 3 / ((p:ℝ) * ((p:ℝ) - 1)) := fun p => by simp [hhv]
  have hv2 : ∀ p : ℕ, hv p 2 = -((p:ℝ) + 3) / ((p:ℝ) ^ 2 * ((p:ℝ) - 1)) := fun p => by simp [hhv]
  have hv3 : ∀ p : ℕ, hv p 3 = 1 / ((p:ℝ) ^ 3 * ((p:ℝ) - 1)) := fun p => by simp [hhv]
  have hv4 : ∀ p e : ℕ, 4 ≤ e → hv p e = 0 := fun p e he => by
    simp only [hhv]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  have hId : F = Hf * (R * Dd) := by
    clear hreindex hT hsumlog hcore htail hHpos hA₀ hA₀0 hF hR hDd
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hFm _
      (hHf_mul.mul (hRm.mul hDdm))]
    intro p k hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    rcases k with _ | k
    · simp only [pow_zero, hFm.map_one, (hHf_mul.mul (hRm.mul hDdm)).map_one]
    rw [hFpp p k hp, mul_apply_prime_pow _ _ hp]
    simp only [hHf_pp p _ hp, hGpp p _ hp]
    rcases k with _ | _ | _ | m
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, hv0, hv1]
      norm_num
      field_simp
      ring
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, hv0, hv1, hv2]
      norm_num
      field_simp
      ring
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, hv0, hv1, hv2, hv3]
      norm_num
      field_simp
      ring
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : 4 ≤ m + 3 + 1 + 1),
        Finset.sum_eq_zero (s := Finset.Ico 4 _) (fun j hj => by
          rw [Finset.mem_Ico] at hj; rw [hv4 p j hj.1, zero_mul])]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hv0, hv1, hv2, hv3]
      have e1 : m + 3 + 1 - 0 = m + 4 := rfl
      have e2 : m + 3 + 1 - 1 = m + 3 := rfl
      have e3 : m + 3 + 1 - 2 = m + 2 := rfl
      have e4 : m + 3 + 1 - 3 = m + 1 := rfl
      rw [e1, e2, e3, e4]
      push_cast
      field_simp
      ring
  clear hGpp hFpp hFm hF0 hRm hDdm hHf_pp hv0 hv1 hv2 hv3 hv4 hhv hv hHf_mul
  have hD : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (R * Dd) k - Real.log y ^ 3 / 6| ≤ K₂ * (1 + Real.log y) ^ 2 := by
    clear hcore htail hHpos hA₀ hA₀0 hF hId
    obtain ⟨K₁, hK₁0, hK₁⟩ := hT
    refine ⟨K₁ + 1, by linarith, fun y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    have hL : 0 ≤ Real.log y := Real.log_nonneg hy
    rw [hreindex R Dd y]
    simp only [hDd]
    obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s = Finset.Icc 1 ⌊y⌋₊ := ⟨_, rfl⟩
    have hS := hsumlog y hy
    rw [← hs] at hS ⊢
    have hmem : ∀ a ∈ s, 1 ≤ (a : ℝ) ∧ (a : ℝ) ≤ y := by
      intro a ha
      rw [hs, Finset.mem_Icc] at ha
      exact ⟨by exact_mod_cast ha.1, (Nat.le_floor_iff hy0.le).1 ha.2⟩
    have hterm : ∀ a ∈ s, R a * ∑ k ∈ Finset.Icc 1 ⌊y / a⌋₊, (k.divisors.card : ℝ) / k
        = 1 / 2 * ((Real.log y - Real.log a) ^ 2 / a)
          + (a : ℝ)⁻¹ * (∑ k ∈ Finset.Icc 1 ⌊y / a⌋₊, (k.divisors.card : ℝ) / k
              - 1 / 2 * Real.log (y / a) ^ 2) := by
      intro a ha
      have ha1 := (hmem a ha).1
      rw [hR, Real.log_div hy0.ne' (by positivity)]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    have herr : |∑ a ∈ s, (a : ℝ)⁻¹ * (∑ k ∈ Finset.Icc 1 ⌊y / a⌋₊, (k.divisors.card : ℝ) / k
              - 1 / 2 * Real.log (y / a) ^ 2)| ≤ K₁ * (1 + Real.log y) * (1 + Real.log y) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hharm : ∑ a ∈ s, (a : ℝ)⁻¹ ≤ 1 + Real.log y := by
        have h1 := harmonic_le_one_add_log ⌊y⌋₊
        rw [harmonic_eq_sum_Icc] at h1
        push_cast at h1
        rw [hs]
        have h2 : Real.log ⌊y⌋₊ ≤ Real.log y := by
          rcases Nat.eq_zero_or_pos ⌊y⌋₊ with h | h
          · rw [h]; simp [hL]
          · exact Real.log_le_log (by exact_mod_cast h) (Nat.floor_le hy0.le)
        linarith
      calc ∑ a ∈ s, |(a : ℝ)⁻¹ * (∑ k ∈ Finset.Icc 1 ⌊y / a⌋₊, (k.divisors.card : ℝ) / k
              - 1 / 2 * Real.log (y / a) ^ 2)|
          ≤ ∑ a ∈ s, (a : ℝ)⁻¹ * (K₁ * (1 + Real.log y)) := by
            refine Finset.sum_le_sum fun a ha => ?_
            have ha1 := (hmem a ha).1
            have hya : 1 ≤ y / a := by rw [le_div_iff₀ (by linarith)]; linarith [(hmem a ha).2]
            rw [abs_mul, abs_of_pos (by positivity)]
            refine mul_le_mul_of_nonneg_left ((hK₁ (y / a) hya).trans ?_) (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ hK₁0
            have : Real.log (y / a) ≤ Real.log y :=
              Real.log_le_log (by positivity) (div_le_self hy0.le ha1)
            linarith
        _ = K₁ * (1 + Real.log y) * ∑ a ∈ s, (a : ℝ)⁻¹ := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ K₁ * (1 + Real.log y) * (1 + Real.log y) :=
            mul_le_mul_of_nonneg_left hharm (by positivity)
    rw [abs_le] at hS herr ⊢
    have := mul_nonneg hK₁0 (mul_nonneg hL hL)
    constructor <;> linarith
  clear hT hsumlog hR hDd
  -- assembly
  obtain ⟨K₂, hK₂0, hK₂⟩ := hD
  refine ⟨(∑' m, Hf m) / 6, by positivity, (9 * K₂ + 3) * A₀, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log x := ⟨_, rfl⟩
  have hL2 : 1 / 2 ≤ L := by
    have := Real.log_le_log (by norm_num) hx
    have := Real.log_two_gt_d9
    rw [hL]; linarith
  have hL4 : L ≤ 4 * x ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [hL]; linarith
  rw [← hL]
  rw [Finset.sum_congr rfl fun n _ => (hF n).symm, hId, hreindex]
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s = Finset.Icc 1 ⌊x⌋₊ := ⟨_, rfl⟩
  have htl := htail x (by linarith)
  rw [← hs] at htl ⊢
  have hsplit : ∑ m ∈ s, Hf m * ∑ k ∈ Finset.Icc 1 ⌊x / m⌋₊, (R * Dd) k
        - (∑' m, Hf m) / 6 * L ^ 3
      = ∑ m ∈ s, Hf m * (∑ k ∈ Finset.Icc 1 ⌊x / m⌋₊, (R * Dd) k - L ^ 3 / 6)
        + L ^ 3 / 6 * (∑ m ∈ s, Hf m - ∑' m, Hf m) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hsplit]
  have hterm : ∀ m ∈ s, |Hf m * (∑ k ∈ Finset.Icc 1 ⌊x / m⌋₊, (R * Dd) k - L ^ 3 / 6)|
      ≤ (|Hf m| * (m : ℝ) ^ ((1 : ℝ) / 4)) * ((9 * K₂ + 2) * L ^ 2) := by
    intro m hm
    rw [hs, Finset.mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hmx : (m : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).1 hm.2
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log m := ⟨_, rfl⟩
    have hℓ0 : 0 ≤ ℓ := hℓ ▸ Real.log_nonneg hm1
    have hℓL : ℓ ≤ L := by rw [hℓ, hL]; exact Real.log_le_log (by linarith) hmx
    obtain ⟨w, hw⟩ : ∃ w, w = (m : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
    have hw1 : 1 ≤ w := hw ▸ Real.one_le_rpow hm1 (by norm_num)
    have hℓw : ℓ ≤ 4 * w := by
      have := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ m)
        (show (0 : ℝ) < 1 / 4 by norm_num)
      rw [hℓ, hw]; linarith only [this]
    have hxm : 1 ≤ x / m := by rw [le_div_iff₀ (by linarith only [hm1])]; linarith only [hmx]
    have hD1 := hK₂ (x / m) hxm
    rw [Real.log_div hx0.ne' (by linarith), ← hL, ← hℓ] at hD1
    rw [← hw, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcore L ℓ w K₂ _ hℓ0 hℓL hL2 hw1 hℓw hK₂0 hD1) (abs_nonneg _)
  have hsum1 : |∑ m ∈ s, Hf m * (∑ k ∈ Finset.Icc 1 ⌊x / m⌋₊, (R * Dd) k - L ^ 3 / 6)|
      ≤ A₀ * ((9 * K₂ + 2) * L ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by positivity)
      (hA₀ (⌊x⌋₊ + 1))
    intro m hm
    rw [hs, Finset.mem_Icc] at hm
    rw [Finset.mem_range]; omega
  have hsum2 : |L ^ 3 / 6 * (∑ m ∈ s, Hf m - ∑' m, Hf m)| ≤ A₀ * L ^ 2 := by
    have hx4 : 0 < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc L ^ 3 / 6 * |∑ m ∈ s, Hf m - ∑' m, Hf m|
        ≤ L ^ 3 / 6 * (A₀ / x ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left htl (by positivity)
      _ = A₀ * L ^ 2 * (L / x ^ ((1 : ℝ) / 4)) / 6 := by ring
      _ ≤ A₀ * L ^ 2 * 4 / 6 := by
          gcongr
          rw [div_le_iff₀ hx4]; linarith
      _ ≤ A₀ * L ^ 2 := by have := mul_nonneg hA₀0 (sq_nonneg L); linarith
  refine (abs_add_le _ _).trans ?_
  linarith only [hsum1, hsum2]


end ArithmeticFunction
