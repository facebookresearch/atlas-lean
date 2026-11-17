/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import MathlibExt.Analysis.PerronKernel
import MathlibExt.NumberTheory.LSeries.VerticalLine
import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormula
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Chebyshev function twisted by a Dirichlet character, and Perron's formula

## Main definitions

* `DirichletCharacter.chebyshevPsi χ x`: `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`, with the same inclusive
  real cutoff as `Chebyshev.psi`.

## Main statements

* `DirichletCharacter.chebyshevPsi_eq_sum_Iic`: the sum may include `n = 0`, since `Λ(0) = 0`.
* `DirichletCharacter.norm_chebyshevPsi_sub_truncated_integral_le`: the truncated Perron formula
  `ψ(x, χ) = (1/2π) ∫_{-R}^{R} -L'/L(c + it, χ) x^{c+it}/(c + it) dt + O(∑ Λ(n) (x/n)^c /
  (R |log (x/n)|))`.
* `DirichletCharacter.exists_norm_chebyshevPsi_sub_truncated_integral_le_log_sq`: at
  `c = 1 + 1/log x` and `x ∈ ℕ + 1/2`, the error is `O(x log² x / R)` uniformly in `χ`.
* `DirichletCharacter.tendsto_truncated_integral_chebyshevPsi`: Perron's formula for `ψ(x, χ)`.
-/

@[expose] public section

open ArithmeticFunction Complex Filter Topology

namespace DirichletCharacter

variable {q : ℕ}

/-- **The twisted Chebyshev function** `ψ(x, χ) = ∑_{0 < n ≤ x} χ(n) Λ(n)`, valued in `ℂ`. -/
noncomputable def chebyshevPsi (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * (vonMangoldt n : ℂ)

/-- `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`, the sum including `n = 0` since `Λ(0) = 0`. -/
theorem chebyshevPsi_eq_sum_Iic (χ : DirichletCharacter ℂ q) (x : ℝ) :
    χ.chebyshevPsi x = ∑ n ∈ Finset.Iic ⌊x⌋₊, χ n * (vonMangoldt n : ℂ) := by
  rw [chebyshevPsi, ← Finset.Icc_bot, show (⊥ : ℕ) = 0 from rfl,
    ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
  simp

/-! ### Perron's formula for `ψ(x, χ)` -/

/-- **The truncated Perron formula for `ψ(x, χ)`.** For real `x > 1` not a prime power, `c > 1`
and `R > 0`,
`‖ψ(x, χ) - (1/2π) ∫_{-R}^{R} -L'/L(c + it, χ) x^{c+it}/(c + it) dt‖
  ≤ (1/π) ∑ Λ(n) (x/n)^c / (R |log (x/n)|)`. -/
theorem norm_chebyshevPsi_sub_truncated_integral_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c R : ℝ} (hx : 1 < x)
    (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) (hc : 1 < c) (hR : 0 < R) :
    ‖χ.chebyshevPsi x - (1 / (2 * Real.pi)) *
        ∫ t in (-R)..R, -(deriv (LFunction χ) (c + t * I) / LFunction χ (c + t * I)) *
          ((x : ℂ) ^ (c + t * I) / (c + t * I))‖ ≤
      1 / Real.pi * ∑' n : ℕ, Λ n * (x / n) ^ c / (R * |Real.log (x / n)|) := by
  classical
  open LSeries.notation in
  have hx0 : 0 < x := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  set a : ℕ → ℂ := fun n => χ n * (Λ n : ℂ) with ha
  have hnorm_a : ∀ n, ‖a n‖ ≤ Λ n := by
    intro n
    simp only [ha, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (norm_le_one χ _)
  have hsumΛ : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖ :=
    (LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc)).norm
  have hsum : LSeriesSummable a (c : ℂ) :=
    Summable.of_norm_bounded hsumΛ (fun n => LSeries.norm_term_le (c : ℂ) (by
      simpa [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg] using hnorm_a n))
  have hzne : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    exact hc0.ne' (by simpa using congrArg Complex.re h)
  have hre : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * I).re = c := by intro t; simp
  have hΛx : ∀ n : ℕ, (n : ℝ) = x → Λ n = 0 := fun n hn =>
    vonMangoldt_eq_zero_iff.mpr (hpp n hn)
  -- the weights
  set w : ℕ → ℝ := fun n => x ^ c * ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖ with hwdef
  have hwS : Summable w := hsumΛ.mul_left _
  have hwval : ∀ n : ℕ, n ≠ 0 → w n = Λ n * (x / n) ^ c := by
    intro n hn
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    simp only [hwdef, LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos hn0, Complex.ofReal_re, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    rw [Real.div_rpow hx0.le (Nat.cast_nonneg n)]
    ring
  set B : ℕ → ℝ := fun n => Λ n * (x / n) ^ c / (R * |Real.log (x / n)|) with hBdef
  have hB0 : ∀ n, 0 ≤ B n := fun n =>
    div_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity)) (by positivity)
  have hBs : Summable B := by
    refine Summable.of_norm_bounded_eventually_nat (hwS.div_const (R * Real.log 2)) ?_
    filter_upwards [eventually_ge_atTop ⌈2 * x⌉₊, eventually_ge_atTop 1] with n hn hn1
    have hn2 : 2 * x ≤ n := Nat.ceil_le.mp hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hlog : Real.log 2 ≤ |Real.log (x / n)| := by
      have h1 : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hnpos]; linarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [one_div, Real.log_inv] at h2
      rw [abs_of_neg (by linarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)])]; linarith
    rw [Real.norm_of_nonneg (hB0 n), hwval n (by omega)]
    exact div_le_div_of_nonneg_left (mul_nonneg vonMangoldt_nonneg (by positivity))
      (mul_pos hR (Real.log_pos one_lt_two)) (mul_le_mul_of_nonneg_left hlog hR.le)
  -- the truncated kernels
  set K : ℕ → ℂ := fun n => PerronKernel.perronKernel (x / n) c R with hKdef
  set D : ℕ → ℂ := fun n => a n * (if 1 < x / n then 1 else 0) with hDdef
  have hkey : ∀ n : ℕ, ‖D n - a n * K n‖ ≤ B n / Real.pi := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hDdef, ha, hBdef]
    rcases eq_or_ne (n : ℝ) x with hnx | hnx
    · simp [hDdef, ha, hBdef, hΛx n hnx]
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hxn : 0 < x / n := div_pos hx0 hnR
    have hxn1 : x / n ≠ 1 := fun h => hnx ((div_eq_one_iff_eq hnR.ne').mp h).symm
    have hb := PerronKernel.perron_bound hxn hxn1 hc0 hR
    rw [← Real.rpow_def_of_pos hxn] at hb
    rw [show D n - a n * K n = -(a n * (K n - (if 1 < x / n then (1 : ℂ) else 0))) by
      simp only [hDdef]; ring, norm_neg, norm_mul]
    calc ‖a n‖ * ‖K n - (if 1 < x / n then (1 : ℂ) else 0)‖
        ≤ Λ n * ((x / n) ^ c / |Real.log (x / n)| / R / Real.pi) :=
          mul_le_mul (hnorm_a n) hb (norm_nonneg _) vonMangoldt_nonneg
      _ = B n / Real.pi := by
          simp only [hBdef]
          ring
  -- the interchange of the sum and the truncated integral
  have hHS : HasSum (fun n : ℕ => a n * K n)
      ((1 / (2 * Real.pi)) * ∫ t in (-R)..R,
        LSeries a ((c : ℂ) + (t : ℂ) * I) * ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          ((c : ℂ) + (t : ℂ) * I))) := by
    have hKc : Continuous fun t : ℝ =>
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) :=
      (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx0.ne'))).div
        (by fun_prop) hzne
    have hmain := hsum.hasSum_intervalIntegral_term_vertical_mul hKc (B := x ^ c / c) (fun t => by
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
      exact div_le_div_of_nonneg_left (by positivity) hc0
        ((hre t).symm.le.trans (Complex.re_le_norm _))) R
    refine (hmain.mul_left (1 / (2 * Real.pi) : ℂ)).congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha]
    · simp only [hKdef, PerronKernel.perronKernel]
      rw [show (fun t : ℝ => LSeries.term a ((c : ℂ) + (t : ℂ) * I) n *
          ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))) =
          fun t : ℝ => a n * ((((x / n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
            ((c : ℂ) + (t : ℂ) * I)) from funext fun t => by
              rw [← LSeries.term_mul_cpow_div a hn hx0, mul_div_assoc],
        intervalIntegral.integral_const_mul]
      push_cast
      ring
  -- the discrete sum
  have hDzero : ∀ n : ℕ, n ∉ Finset.Icc 1 ⌊x⌋₊ → D n = 0 := by
    intro n hnmem
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hDdef, ha]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnx : ¬ ((n : ℝ) ≤ x) := fun hlt => hnmem (Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hn, Nat.le_floor hlt⟩)
      have hlt1 : ¬ 1 < x / n := by
        rw [lt_div_iff₀ hnR, one_mul]; exact fun h => hnx h.le
      simp [hDdef, hlt1]
  have hDsum : ∑' n, D n = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
    rw [tsum_eq_sum hDzero]
    refine Finset.sum_congr rfl fun n hnmem => ?_
    simp only [Finset.mem_Icc] at hnmem
    have hn : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hnmem.1
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hnmem.2
    rcases eq_or_ne (n : ℝ) x with hnx | hnx
    · simp [hDdef, ha, hΛx n hnx]
    have hgt1 : 1 < x / n := by
      rw [lt_div_iff₀ hnR, one_mul]; exact lt_of_le_of_ne hnle hnx
    simp [hDdef, hgt1]
  have hDsummable : Summable D := summable_of_ne_finset_zero hDzero
  have hpsi : χ.chebyshevPsi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
    rw [chebyshevPsi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  have hint : (∫ t in (-R)..R, -(deriv (LFunction χ) (c + t * I) / LFunction χ (c + t * I)) *
        ((x : ℂ) ^ (c + t * I) / (c + t * I))) =
      ∫ t in (-R)..R, LSeries a ((c : ℂ) + (t : ℂ) * I) *
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre' : 1 < ((c : ℂ) + (t : ℂ) * I).re := by rw [hre]; exact hc
    have hLS : LSeries a ((c : ℂ) + (t : ℂ) * I) =
        -(deriv (LFunction χ) ((c : ℂ) + t * I) / LFunction χ ((c : ℂ) + t * I)) := by
      have := LSeries_twist_vonMangoldt_eq χ hre'
      rw [deriv_LFunction_eq_deriv_LSeries χ hre', LFunction_eq_LSeries χ hre', ← neg_div]
      exact this
    rw [hLS]
  have hns : Summable fun n => ‖D n - a n * K n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hkey (hBs.div_const _)
  rw [hint, hpsi, ← hDsum, ← hHS.tsum_eq, ← hDsummable.tsum_sub hHS.summable]
  calc ‖∑' n, (D n - a n * K n)‖ ≤ ∑' n, ‖D n - a n * K n‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n, B n / Real.pi := hns.tsum_le_tsum hkey (hBs.div_const _)
    _ = 1 / Real.pi * ∑' n, B n := by rw [tsum_div_const]; ring

/-- **The truncated Perron formula for `ψ(x, χ)` at `c = 1 + 1/log x`.** There is an absolute
constant `C` such that for every Dirichlet character `χ`, when `x - 1/2` is a positive integer and
`T > 0`, with `c = 1 + 1/log x`,
`‖ψ(x, χ) - (1/2π) ∫_{-T}^{T} -L'/L(c + it, χ) x^{c+it}/(c + it) dt‖ ≤ C x log² x / T`. -/
theorem exists_norm_chebyshevPsi_sub_truncated_integral_le_log_sq :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x T : ℝ),
      (∃ n : ℕ, 0 < n ∧ x = n + 1 / 2) → 0 < T →
      ‖χ.chebyshevPsi x - (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
          -(deriv (LFunction χ) ((1 + 1 / Real.log x : ℝ) + t * I) /
              LFunction χ ((1 + 1 / Real.log x : ℝ) + t * I)) *
            ((x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I))‖ ≤
        C * (x * Real.log x ^ 2 / T) := by
  obtain ⟨C₂, hC₂⟩ := exists_tsum_vonMangoldt_mul_div_abs_log_le
  refine ⟨C₂ / Real.pi, fun {q} _ χ x T hxn hT => ?_⟩
  obtain ⟨m, hm, hxm⟩ := hxn
  have hx : 1 < x := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hxm]; linarith
  have hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n := by
    intro n hn
    exfalso
    have h3 : ((((n : ℤ) - m) : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
    rcases le_or_gt ((n : ℤ) - m) 0 with h | h
    · have : ((((n : ℤ) - m) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
      linarith
    · have : (1 : ℝ) ≤ ((((n : ℤ) - m) : ℤ) : ℝ) := by exact_mod_cast h
      linarith
  have hc : 1 < 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := one_div_pos.mpr (Real.log_pos hx)
    linarith
  have h1 := norm_chebyshevPsi_sub_truncated_integral_le χ hx hpp hc hT
  have h2 := (hC₂ x T ⟨m, hm, hxm⟩ hT).2
  refine h1.trans ?_
  calc 1 / Real.pi * _ ≤ 1 / Real.pi * (C₂ * (x * Real.log x ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C₂ / Real.pi * (x * Real.log x ^ 2 / T) := by ring


/-- **Perron's formula for `ψ(x, χ)`.** For real `x > 1` not a prime power and `c > 1`,
`(1/2π) ∫_{-R}^{R} -L'/L(c + it, χ) x^{c+it}/(c + it) dt → ψ(x, χ)` as `R → ∞`. -/
theorem tendsto_truncated_integral_chebyshevPsi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 1 < x) (hpp : ∀ n : ℕ, (n : ℝ) = x → ¬ IsPrimePow n) (hc : 1 < c) :
    Tendsto (fun R : ℝ => (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R)..R,
        -(deriv (LFunction χ) (c + t * I) / LFunction χ (c + t * I)) *
          ((x : ℂ) ^ (c + t * I) / (c + t * I))) atTop (𝓝 (χ.chebyshevPsi x)) := by
  set S : ℝ := ∑' n : ℕ, Λ n * (x / n) ^ c / |Real.log (x / n)| with hS
  have hlim : Tendsto (fun R : ℝ => 1 / Real.pi * (R⁻¹ * S)) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero.mul_const S).const_mul (1 / Real.pi))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [norm_sub_rev]
  refine (norm_chebyshevPsi_sub_truncated_integral_le χ hx hpp hc hR).trans (le_of_eq ?_)
  congr 1
  rw [hS, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [mul_comm R, ← div_div, div_eq_inv_mul _ R]


end DirichletCharacter
