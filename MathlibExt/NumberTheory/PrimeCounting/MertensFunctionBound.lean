/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusSummatory
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import MathlibExt.NumberTheory.LSeries.Perron
import MathlibExt.NumberTheory.LSeries.PerronError
import MathlibExt.NumberTheory.LSeries.RiemannZetaBounds
import MathlibExt.NumberTheory.PrimeCounting.AverageOmegaHFree

/-!
# A bound for the Mertens function

Using the zero-free region `|ζ(σ + it)| > c / log⁷ T` for `1 - c' / log⁹ T ≤ σ ≤ 2`, a
logarithmically weighted Perron formula and a contour shift, we prove that the Mertens function
`M(x) = ∑_{n ≤ x} μ(n)` satisfies `M(x) = O(x exp(-c (log x)^{1/10}))` for some `c > 0`.

## Main statements

* `ArithmeticFunction.mertens_isBigO_mul_exp_neg_mul_log_rpow`: the bound for `M(x)`.
* `ArithmeticFunction.sum_moebius_isBigO_mul_exp_neg_mul_log_rpow`: the same bound, written as a
  sum of real numbers.
* `Nat.card_squarefree_sub_isBigO_sqrt`: the number of squarefree `n ≤ x` is
  `6 x / π² + O(√x)`.
* `Nat.card_squarefree_even_cardFactors_sub_isBigO`: the number of squarefree `n ≤ x` with an
  even number of prime factors is `3 x / π² + O(x exp(-c (log x)^{1/10}))`.
-/

@[expose] public section

open Asymptotics Filter Complex MeasureTheory

namespace ArithmeticFunction

/-- **A bound for the summatory function of `μ`.** There is `c > 0` with
`∑_{n ≤ x} μ(n) = O(x exp(-c (log x) ^ (1 / 10)))`. -/
theorem sum_moebius_isBigO_mul_exp_neg_mul_log_rpow :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ))
        =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
  classical
  -- ## Part A: the smoothed sum `M₁ (x) = ∑_{n ≤ x} μ n * log (x / n)`
  have hA : ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, Real.exp 1024 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (x / n)|
        ≤ K * (x * Real.exp (-b * Real.log x ^ (1 / 10 : ℝ))) := by
    obtain ⟨c₁, c₂, hc₁, hc₂, hzf⟩ := exists_pos_div_log_pow_seven_lt_norm_riemannZeta
    obtain ⟨δ, hδ, M₀, hM₀, hbox⟩ := exists_riemannZeta₁_ne_zero_and_norm_logDeriv_le
    -- `(s - 1) / ζ₁ s` is bounded on the box `1 - δ ≤ Re s ≤ 2`, `|Im s| ≤ 1`
    obtain ⟨M, hM, hMbox⟩ : ∃ M > 0, ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 →
        ‖(s - 1) / riemannZeta₁ s‖ ≤ M := by
      have hK : IsCompact ((Set.Icc (1 - δ) 2) ×ℂ (Set.Icc (-1 : ℝ) 1)) :=
        IsCompact.reProdIm isCompact_Icc isCompact_Icc
      have hcont : ContinuousOn (fun s => (s - 1) / riemannZeta₁ s)
          ((Set.Icc (1 - δ) 2) ×ℂ (Set.Icc (-1 : ℝ) 1)) := by
        intro s hs
        obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := Complex.mem_reProdIm.mp hs
        exact ((continuous_id.sub continuous_const).continuousAt.div
          (differentiable_riemannZeta₁.continuous.continuousAt)
          (hbox s hr1 hr2 (abs_le.mpr ⟨hi1, hi2⟩)).1).continuousWithinAt
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
      refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun s h1 h2 h3 => ?_⟩
      obtain ⟨him1, him2⟩ := abs_le.mp h3
      exact le_trans (hC s (Complex.mem_reProdIm.mpr ⟨⟨h1, h2⟩, him1, him2⟩)) (le_max_left _ _)
    -- `ζ₁` does not vanish on `Re s ≥ 1`
    have hne_one : ∀ s : ℂ, 1 ≤ s.re → riemannZeta₁ s ≠ 0 := by
      intro s hs
      rcases eq_or_ne s 1 with rfl | hs1
      · simp
      · have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
        rw [riemannZeta_eq_inv_sub_mul hs1] at hz
        exact fun h => hz (by rw [h, mul_zero])
    -- `L μ = (s - 1) / ζ₁ s` on `Re s > 1`
    have hLeq : ∀ s : ℂ, 1 < s.re →
        LSeries (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s
          = (s - 1) / riemannZeta₁ s := by
      intro s hs
      have h1 := LSeries_one_mul_Lseries_moebius hs
      rw [LSeries_one_eq_riemannZeta hs] at h1
      have hs1 : s ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hs
        exact lt_irrefl _ hs
      rw [riemannZeta_eq_inv_sub_mul hs1] at h1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hz : riemannZeta₁ s ≠ 0 := hne_one s hs.le
      rw [eq_div_iff hz]
      field_simp at h1
      linear_combination h1
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = min c₁ (min δ (1 / 2)) := ⟨_, rfl⟩
    have ha0 : 0 < a := by rw [ha_def]; positivity
    have hac₁ : a ≤ c₁ := by rw [ha_def]; exact min_le_left _ _
    have haδ : a ≤ δ := by rw [ha_def]; exact (min_le_right _ _).trans (min_le_left _ _)
    have ha2 : a ≤ 1 / 2 := by rw [ha_def]; exact (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨K₁, hK₁⟩ : ∃ K : ℝ, K = 1 / c₂ + M := ⟨_, rfl⟩
    obtain ⟨K₂, hK₂⟩ : ∃ K : ℝ, K = 6 + 4 * K₁ := ⟨_, rfl⟩
    obtain ⟨K₃, hK₃⟩ : ∃ K : ℝ, K = (Nat.factorial 10 : ℝ) * (2 / a) ^ 10 := ⟨_, rfl⟩
    have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
    have hK₂0 : 0 < K₂ := by rw [hK₂]; positivity
    have hK₃0 : 0 < K₃ := by rw [hK₃]; positivity
    refine ⟨a / 2, by positivity, by linarith, K₂ * K₃, by positivity, fun x hx => ?_⟩
    -- ## Scale facts: `L = log x`, `U = L ^ (1 / 10)`, `T = exp U`
    have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
    have hx0 : 0 < x := by linarith
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
    have hL : 1024 ≤ L := by
      have h := Real.log_le_log (Real.exp_pos 1024) hx
      rwa [Real.log_exp, ← hLdef] at h
    have hL0 : 0 < L := by linarith
    obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = L ^ (1 / 10 : ℝ) := ⟨_, rfl⟩
    have hU0 : 0 < U := hUdef ▸ Real.rpow_pos_of_pos hL0 _
    have hU10 : U ^ 10 = L := by
      rw [hUdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
    have hU2 : 2 ≤ U := by
      by_contra h
      push Not at h
      have h' := pow_lt_pow_left₀ h hU0.le (by norm_num : (10 : ℕ) ≠ 0)
      rw [hU10] at h'
      norm_num at h'
      linarith
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = U ^ 9 := ⟨_, rfl⟩
    have hQ1 : 1 ≤ Q := hQdef ▸ one_le_pow₀ (by linarith)
    have hQ0 : 0 < Q := by linarith
    have hLQ : L = U * Q := by rw [← hU10, hQdef]; ring
    obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = x * Real.exp (-a * U) := ⟨_, rfl⟩
    have hP0 : 0 < P := by rw [hPdef]; positivity
    -- the final comparison `U ^ 10 * exp (-a U) ≤ K₃ * exp (-(a / 2) U)`
    have hfinal : U ^ 10 * P ≤ K₃ * (x * Real.exp (-(a / 2) * U)) := by
      have hy : 0 ≤ a * U / 2 := by positivity
      have hexp := Real.pow_div_factorial_le_exp (a * U / 2) hy 10
      have hfac : (0 : ℝ) < (Nat.factorial 10 : ℝ) := by positivity
      have hU10' : U ^ 10 ≤ K₃ * Real.exp (a * U / 2) := by
        rw [div_le_iff₀ hfac] at hexp
        have hsplit : U ^ 10 = (2 / a) ^ 10 * (a * U / 2) ^ 10 := by
          field_simp
        rw [hsplit, hK₃]
        calc (2 / a) ^ 10 * (a * U / 2) ^ 10
            ≤ (2 / a) ^ 10 * (Real.exp (a * U / 2) * (Nat.factorial 10 : ℝ)) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ = (Nat.factorial 10 : ℝ) * (2 / a) ^ 10 * Real.exp (a * U / 2) := by ring
      have hsum : Real.exp (a * U / 2) * Real.exp (-a * U) = Real.exp (-(a / 2) * U) := by
        rw [← Real.exp_add]; ring_nf
      rw [hPdef]
      calc U ^ 10 * (x * Real.exp (-a * U))
          ≤ K₃ * Real.exp (a * U / 2) * (x * Real.exp (-a * U)) :=
            mul_le_mul_of_nonneg_right hU10' (by positivity)
        _ = K₃ * (x * (Real.exp (a * U / 2) * Real.exp (-a * U))) := by ring
        _ = K₃ * (x * Real.exp (-(a / 2) * U)) := by rw [hsum]
    have hmain : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (x / n)| ≤ K₂ * (U ^ 10 * P) := by
      -- ## The abscissae `c₀ = 1 + 1 / L`, `σ₁ = 1 - a / U ^ 9` and the height `T = exp U`
      obtain ⟨c₀, hc₀def⟩ : ∃ c : ℝ, c = 1 + 1 / L := ⟨_, rfl⟩
      obtain ⟨σ₁, hσ₁def⟩ : ∃ σ : ℝ, σ = 1 - a / Q := ⟨_, rfl⟩
      obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp U := ⟨_, rfl⟩
      have hinvL : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
      have hinvL0 : 0 < 1 / L := by positivity
      have hc₀1 : 1 < c₀ := by linarith
      have hc₀2 : c₀ ≤ 2 := by linarith
      have haQ0 : 0 < a / Q := by positivity
      have haQ : a / Q ≤ a := div_le_self ha0.le hQ1
      have hσ₁1 : σ₁ < 1 := by linarith
      have hσ₁h : 1 / 2 ≤ σ₁ := by linarith
      have hσ₁c₀ : σ₁ ≤ c₀ := by linarith
      have hσ₁δ : 1 - δ ≤ σ₁ := by linarith
      have hlogT : Real.log T = U := by rw [hTdef, Real.log_exp]
      have hT2 : Real.exp 2 ≤ T := by rw [hTdef]; exact Real.exp_le_exp.mpr hU2
      have hT1 : 1 ≤ T := le_trans (Real.one_le_exp (by norm_num)) hT2
      have hT0 : 0 < T := by linarith
      have hσ₁c₁ : 1 - c₁ / Real.log T ^ 9 ≤ σ₁ := by
        rw [hlogT, ← hQdef, hσ₁def]
        have := div_le_div_of_nonneg_right hac₁ hQ0.le
        linarith
      -- ## `x ^ σ` at the two abscissae
      have hxc₀ : x ^ c₀ ≤ 3 * x := by
        have h1 : x ^ c₀ = x * Real.exp 1 := by
          rw [Real.rpow_def_of_pos hx0, ← hLdef, hc₀def,
            show L * (1 + 1 / L) = L + 1 by field_simp, Real.exp_add, hLdef, Real.exp_log hx0]
        have h2 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        rw [h1, mul_comm 3 x]
        exact mul_le_mul_of_nonneg_left h2.le hx0.le
      have hxu : ∀ u : ℝ, u ≤ c₀ → x ^ u ≤ 3 * x := fun u hu =>
        (Real.rpow_le_rpow_of_exponent_le hx1 hu).trans hxc₀
      have hxσ₁ : x ^ σ₁ = P := by
        rw [Real.rpow_def_of_pos hx0, ← hLdef, hPdef, hσ₁def,
          show L * (1 - a / Q) = L + -a * U by rw [hLQ]; field_simp; ring,
          Real.exp_add, hLdef, Real.exp_log hx0]
      have hTP : x / T ≤ P := by
        rw [hPdef, hTdef, div_eq_mul_inv, ← Real.exp_neg]
        gcongr
        nlinarith only [ha2, hU0]
      have hT2P : x / T ^ 2 ≤ P :=
        le_trans (div_le_div_of_nonneg_left hx0.le hT0 (le_self_pow₀ hT1 (by norm_num))) hTP
      -- ## The integrand `F (s) = (s - 1) / ζ₁ (s) * x ^ s / s ^ 2` and its size
      obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun s : ℂ =>
          (s - 1) / riemannZeta₁ s * (x : ℂ) ^ s / s ^ 2 := ⟨_, rfl⟩
      have hFle : ∀ (s : ℂ) (B E N : ℝ), ‖(s - 1) / riemannZeta₁ s‖ ≤ B →
          x ^ s.re ≤ E → 0 < N → N ≤ ‖s‖ ^ 2 → 0 ≤ B → ‖F s‖ ≤ B * E / N := by
        intro s B E N hB hE hN hNs hB0
        have hnorm : ‖F s‖ = ‖(s - 1) / riemannZeta₁ s‖ * x ^ s.re / ‖s‖ ^ 2 := by
          rw [hF]
          simp only [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hx0' : 0 ≤ x ^ s.re := Real.rpow_nonneg hx0.le _
        rw [hnorm]
        calc ‖(s - 1) / riemannZeta₁ s‖ * x ^ s.re / ‖s‖ ^ 2
            ≤ B * E / ‖s‖ ^ 2 := by gcongr
          _ ≤ B * E / N :=
            div_le_div_of_nonneg_left (mul_nonneg hB0 (hx0'.trans hE)) hN hNs
      -- ## Perron: `M₁ (x)` is the vertical integral of `F` on `Re s = c₀`
      obtain ⟨V, hVdef⟩ : ∃ V : ℂ, V = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (Real.log (x / n) : ℂ) := ⟨_, rfl⟩
      have hP : HasVerticalIntegral c₀ F V := by
        have hsum : LSeriesSummable (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (c₀ : ℂ) := by
          refine ArithmeticFunction.LSeriesSummable_moebius_iff.mpr ?_
          simp only [Complex.ofReal_re]
          linarith
        have h := hsum.hasVerticalIntegral_LSeries_mul_cpow_div_pow_succ (k := 1) le_rfl
          (by linarith) hx0
        have hval : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.moebius n : ℤ) : ℂ) * ((Real.log (x / n) : ℂ)) ^ 1) /
              (Nat.factorial 1 : ℂ) = V := by
          rw [hVdef]; simp
        rw [hval] at h
        refine h.congr_line fun t => ?_
        have hre : 1 < ((c₀ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hc₀1
        rw [hF, hLeq _ hre]
      have hVM : ‖V‖ = |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (x / n)| := by
        rw [hVdef, ← Real.norm_eq_abs, ← Complex.norm_real]
        push_cast
        rfl
      -- ## `‖1 / ζ‖ ≤ 1 + L` on the Perron line
      have hline : ∀ s : ℂ, s.re = c₀ → ‖(s - 1) / riemannZeta₁ s‖ ≤ 1 + L := by
        intro s hs
        have hs1 : 1 < s.re := hs ▸ hc₀1
        rw [← hLeq s hs1]
        have hsum : Summable fun n => ‖LSeries.term
            (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ :=
          summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1)
        refine (norm_tsum_le_tsum_norm hsum).trans ?_
        refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun N => ?_
        have hterm : ∀ n : ℕ, ‖LSeries.term
            (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s (n + 1)‖
              ≤ ((n : ℝ) + 1) ^ (-c₀) := by
          intro n
          rw [LSeries.norm_term_eq, ite_eq_right (Nat.succ_ne_zero n), hs,
            Real.rpow_neg (by positivity)]
          push_cast
          rw [div_eq_mul_inv]
          refine mul_le_of_le_one_left (by positivity) ?_
          have := ArithmeticFunction.abs_moebius_le_one (n := n + 1)
          rw [Complex.norm_intCast]
          exact_mod_cast this
        have hterm0 : ‖LSeries.term
            (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s 0‖ = 0 := by
          simp
        calc _ ≤ ∑ n ∈ Finset.range (N + 1), ‖LSeries.term
                (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
                (fun _ _ _ => norm_nonneg _)
          _ = ∑ n ∈ Finset.range N, ‖LSeries.term
                (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s (n + 1)‖ + 0 := by
              rw [Finset.sum_range_succ', hterm0]
          _ ≤ ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-c₀) + 0 := by
              gcongr with n hn
              exact hterm n
          _ ≤ 1 + 1 / (c₀ - 1) := by rw [add_zero]; exact sum_range_add_one_rpow_neg_le hc₀1 N
          _ = 1 + L := by rw [hc₀def]; field_simp; ring
      -- ## Truncation at height `T`
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      have hAt : ∀ t : ℝ, 1 ≤ |t| →
          ‖F ((c₀ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (1 + L) * (3 * x) / t ^ 2 := by
        intro t ht
        have hre : ((c₀ : ℂ) + (t : ℂ) * Complex.I).re = c₀ := by simp
        have him : ((c₀ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
        have hN : t ^ 2 ≤ ‖(c₀ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := by
          have h := Complex.abs_im_le_norm ((c₀ : ℂ) + (t : ℂ) * Complex.I)
          rw [him] at h
          rw [← sq_abs t]
          gcongr
        have ht2 : 0 < t ^ 2 := by
          have h := one_le_pow₀ (n := 2) ht
          rw [sq_abs] at h
          linarith only [h]
        exact hFle _ _ _ _ (hline _ hre) (by rw [hre]; exact hxc₀) ht2 hN (by linarith)
      have htr := hP.norm_sub_le_of_norm_le_div_sq hAt hT1
      -- ## `1 / ζ` on the rectangle `[σ₁, c₀] × [-T, T]`
      have hrect : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c₀ → |s.im| ≤ T →
          riemannZeta₁ s ≠ 0 ∧ ‖(s - 1) / riemannZeta₁ s‖ ≤ K₁ * Q := by
        intro s h1 h2 h3
        have hKQ : K₁ * Q = 1 / c₂ * Q + M * Q := by rw [hK₁]; ring
        have hMQ : M ≤ M * Q := le_mul_of_one_le_right hM.le hQ1
        have hcQ : 0 ≤ 1 / c₂ * Q := by positivity
        rcases le_or_gt |s.im| 1 with him | him
        · have hb := hbox s (by linarith only [h1, hσ₁δ]) (by linarith only [h2, hc₀2]) him
          have hm := hMbox s (by linarith only [h1, hσ₁δ]) (by linarith only [h2, hc₀2]) him
          exact ⟨hb.1, by linarith only [hm, hKQ, hMQ, hcQ]⟩
        · have hz := hzf T hT2 s him.le h3 (by linarith only [h1, hσ₁c₁])
            (by linarith only [h2, hc₀2])
          rw [hlogT] at hz
          have hc₂U : 0 < c₂ / U ^ 7 := by positivity
          have hzne : riemannZeta s ≠ 0 := by
            intro h0
            rw [h0, norm_zero] at hz
            linarith only [hz, hc₂U]
          have hs1 : s ≠ 1 := by
            intro h
            rw [h, Complex.one_im, abs_zero] at him
            linarith only [him]
          have hz1 : riemannZeta₁ s ≠ 0 := by
            rw [riemannZeta_eq_inv_sub_mul hs1] at hzne
            exact fun h0 => hzne (by rw [h0, mul_zero])
          refine ⟨hz1, ?_⟩
          have heq : (s - 1) / riemannZeta₁ s = (riemannZeta s)⁻¹ := by
            rw [riemannZeta_eq_inv_sub_mul hs1, mul_inv, inv_inv, div_eq_mul_inv]
          have hinv : ‖(riemannZeta s)⁻¹‖ ≤ U ^ 7 / c₂ := by
            rw [norm_inv]
            calc ‖riemannZeta s‖⁻¹ ≤ (c₂ / U ^ 7)⁻¹ := inv_anti₀ hc₂U hz.le
              _ = U ^ 7 / c₂ := inv_div _ _
          have hU79 : U ^ 7 ≤ Q := by
            rw [hQdef]
            exact pow_le_pow_right₀ (by linarith only [hU2]) (by norm_num)
          have hUQ : U ^ 7 / c₂ ≤ 1 / c₂ * Q := by
            rw [div_eq_mul_one_div, mul_comm]
            exact mul_le_mul_of_nonneg_left hU79 (by positivity)
          have hMQ0 : 0 ≤ M * Q := by positivity
          rw [heq]
          linarith only [hinv, hUQ, hKQ, hMQ0]
      have hRmem : ∀ s ∈ Set.uIcc σ₁ c₀ ×ℂ Set.uIcc (-T) T,
          σ₁ ≤ s.re ∧ s.re ≤ c₀ ∧ |s.im| ≤ T := by
        intro s hs
        rw [Complex.mem_reProdIm, Set.uIcc_of_le hσ₁c₀,
          Set.uIcc_of_le (by linarith only [hT0] : -T ≤ T)] at hs
        exact ⟨hs.1.1, hs.1.2, abs_le.mpr hs.2⟩
      have hFd : DifferentiableOn ℂ F (Set.uIcc σ₁ c₀ ×ℂ Set.uIcc (-T) T) := by
        intro s hs
        obtain ⟨h1, h2, h3⟩ := hRmem s hs
        have hz := (hrect s h1 h2 h3).1
        have hs0 : s ≠ 0 := by
          intro h
          rw [h, Complex.zero_re] at h1
          linarith only [h1, hσ₁h]
        rw [hF]
        exact ((((differentiableAt_id.sub_const 1).div
          (differentiable_riemannZeta₁ s) hz).mul
          (differentiableAt_id.const_cpow (Or.inl hxC))).div (differentiableAt_id.pow 2)
          (pow_ne_zero 2 hs0)).differentiableWithinAt
      have hcau := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
        ⟨σ₁, -T⟩ ⟨c₀, T⟩ hFd
      obtain ⟨Bt, hBt⟩ : ∃ z : ℂ,
          z = ∫ u : ℝ in σ₁..c₀, F ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
      obtain ⟨Tp, hTp⟩ : ∃ z : ℂ,
          z = ∫ u : ℝ in σ₁..c₀, F ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
      obtain ⟨R, hRdef⟩ : ∃ z : ℂ,
          z = ∫ y : ℝ in (-T)..T, F ((c₀ : ℂ) + (y : ℂ) * Complex.I) := ⟨_, rfl⟩
      obtain ⟨Lf, hLf⟩ : ∃ z : ℂ,
          z = ∫ y : ℝ in (-T)..T, F ((σ₁ : ℂ) + (y : ℂ) * Complex.I) := ⟨_, rfl⟩
      have hcau' : Bt - Tp + Complex.I * R - Complex.I * Lf = 0 := by
        rw [hBt, hTp, hRdef, hLf]
        simpa only [smul_eq_mul] using hcau
      -- ## The two horizontal sides
      have hhor : ∀ y : ℝ, |y| = T →
          ‖∫ u : ℝ in σ₁..c₀, F ((u : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 6 * K₁ * (Q * P) := by
        intro y hy
        have hpt : ∀ u ∈ Set.uIoc σ₁ c₀,
            ‖F ((u : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K₁ * Q * (3 * x) / T ^ 2 := by
          intro u hu
          rw [Set.uIoc_of_le hσ₁c₀] at hu
          have hre : ((u : ℂ) + (y : ℂ) * Complex.I).re = u := by simp
          have him : ((u : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
          have hD := (hrect _ (by rw [hre]; exact hu.1.le) (by rw [hre]; exact hu.2)
            (by rw [him, hy])).2
          have hN : T ^ 2 ≤ ‖(u : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 := by
            have h := Complex.abs_im_le_norm ((u : ℂ) + (y : ℂ) * Complex.I)
            rw [him, hy] at h
            gcongr
          exact hFle _ _ _ _ hD (by rw [hre]; exact hxu u hu.2) (by positivity) hN
            (by positivity)
        have hI := intervalIntegral.norm_integral_le_of_norm_le_const hpt
        have hlen : |c₀ - σ₁| ≤ 2 := by
          rw [abs_of_nonneg (by linarith only [hσ₁c₀])]
          linarith only [hc₀2, hσ₁h]
        have hB0 : 0 ≤ K₁ * Q * (3 * x) / T ^ 2 := by positivity
        calc _ ≤ K₁ * Q * (3 * x) / T ^ 2 * |c₀ - σ₁| := hI
          _ ≤ K₁ * Q * (3 * x) / T ^ 2 * 2 := mul_le_mul_of_nonneg_left hlen hB0
          _ = 6 * (K₁ * Q) * (x / T ^ 2) := by ring
          _ ≤ 6 * (K₁ * Q) * P := mul_le_mul_of_nonneg_left hT2P (by positivity)
          _ = 6 * K₁ * (Q * P) := by ring
      have hBtn : ‖Bt‖ ≤ 6 * K₁ * (Q * P) := by
        rw [hBt]
        exact hhor (-T) (by rw [abs_neg, abs_of_pos hT0])
      have hTpn : ‖Tp‖ ≤ 6 * K₁ * (Q * P) := by
        rw [hTp]
        exact hhor T (abs_of_pos hT0)
      -- ## The left side `Re s = σ₁`
      have hlpt : ∀ y : ℝ, |y| ≤ T →
          ‖F ((σ₁ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 4 * K₁ * (Q * P) * (1 + y ^ 2)⁻¹ := by
        intro y hy
        obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (σ₁ : ℂ) + (y : ℂ) * Complex.I := ⟨_, rfl⟩
        rw [← hs]
        have hre : s.re = σ₁ := by rw [hs]; simp
        have him : s.im = y := by rw [hs]; simp
        have hD := (hrect s (by rw [hre]) (by rw [hre]; exact hσ₁c₀) (by rw [him]; exact hy)).2
        have hN : (1 + y ^ 2) / 4 ≤ ‖s‖ ^ 2 := by
          rw [Complex.sq_norm, hs, Complex.normSq_add_mul_I]
          have hσ₁sq : 1 / 4 ≤ σ₁ ^ 2 := by nlinarith only [hσ₁h]
          have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
          linarith only [hσ₁sq, hy2]
        have hbound := hFle s (K₁ * Q) P ((1 + y ^ 2) / 4) hD (by rw [hre, hxσ₁])
          (by positivity) hN (by positivity)
        have hy1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
        calc _ ≤ K₁ * Q * P / ((1 + y ^ 2) / 4) := hbound
          _ = 4 * K₁ * (Q * P) * (1 + y ^ 2)⁻¹ := by field_simp
      have hLfn : ‖Lf‖ ≤ 4 * Real.pi * K₁ * (Q * P) := by
        have hcont : Continuous fun y : ℝ => 4 * K₁ * (Q * P) * (1 + y ^ 2)⁻¹ :=
          continuous_const.mul ((continuous_const.add (continuous_pow 2)).inv₀
            fun y => (by positivity : (1 : ℝ) + y ^ 2 ≠ 0))
        have hI := intervalIntegral.norm_integral_le_of_norm_le
          (by linarith only [hT0] : -T ≤ T)
          (Filter.Eventually.of_forall fun y hy => hlpt y (abs_le.mpr ⟨hy.1.le, hy.2⟩))
          (hcont.intervalIntegrable (μ := volume) _ _)
        rw [intervalIntegral.integral_const_mul, integral_inv_one_add_sq, Real.arctan_neg] at hI
        have harc : Real.arctan T < Real.pi / 2 := Real.arctan_lt_pi_div_two T
        have hc0 : 0 ≤ 4 * K₁ * (Q * P) := by positivity
        rw [hLf]
        calc _ ≤ 4 * K₁ * (Q * P) * (Real.arctan T - -Real.arctan T) := hI
          _ ≤ 4 * K₁ * (Q * P) * Real.pi :=
            mul_le_mul_of_nonneg_left (by linarith only [harc]) hc0
          _ = 4 * Real.pi * K₁ * (Q * P) := by ring
      -- ## Assembly
      have hpi : 0 < Real.pi := Real.pi_pos
      have hRx : R = Complex.I * Bt - Complex.I * Tp + Lf := by
        linear_combination (-Complex.I) * hcau' + (R - Lf) * Complex.I_sq
      have hIT : (1 / (2 * Real.pi)) • R
          = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * Bt - Complex.I * Tp + Lf) := by
        rw [Complex.real_smul, hRx]
      have hITn : ‖(1 / (2 * Real.pi)) • R‖
          ≤ (1 / (2 * Real.pi)) * (‖Bt‖ + ‖Tp‖ + ‖Lf‖) := by
        rw [hIT, norm_mul, Complex.norm_of_nonneg (by positivity)]
        gcongr
        calc ‖Complex.I * Bt - Complex.I * Tp + Lf‖
            ≤ ‖Complex.I * Bt - Complex.I * Tp‖ + ‖Lf‖ := norm_add_le _ _
          _ ≤ ‖Complex.I * Bt‖ + ‖Complex.I * Tp‖ + ‖Lf‖ := by
            gcongr
            exact norm_sub_le _ _
          _ = ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
      rw [← hRdef] at htr
      have hsplit := norm_le_norm_sub_add V ((1 / (2 * Real.pi)) • R)
      rw [hVM] at hsplit
      -- the truncation error
      have he1 : (1 + L) * (3 * x) / (Real.pi * T) ≤ 3 * P + 3 * (U ^ 10 * P) := by
        have hπT : T ≤ Real.pi * T :=
          le_mul_of_one_le_left hT0.le (by linarith only [hpi, Real.pi_gt_three])
        have hLM0 : 0 ≤ (1 + L) * (3 * x) := by positivity
        calc (1 + L) * (3 * x) / (Real.pi * T) ≤ (1 + L) * (3 * x) / T :=
              div_le_div_of_nonneg_left hLM0 hT0 hπT
          _ = 3 * (1 + L) * (x / T) := by ring
          _ ≤ 3 * (1 + L) * P := mul_le_mul_of_nonneg_left hTP (by positivity)
          _ = 3 * P + 3 * (U ^ 10 * P) := by rw [← hU10]; ring
      -- the contour error
      have he2 : (1 / (2 * Real.pi)) * (‖Bt‖ + ‖Tp‖ + ‖Lf‖) ≤ 4 * (K₁ * (Q * P)) := by
        have hsum3 : ‖Bt‖ + ‖Tp‖ + ‖Lf‖
            ≤ 12 * (K₁ * (Q * P)) + 4 * Real.pi * (K₁ * (Q * P)) := by
          linarith only [hBtn, hTpn, hLfn]
        have hc : 0 ≤ 1 / (2 * Real.pi) := by positivity
        have heq : (1 / (2 * Real.pi)) * (12 * (K₁ * (Q * P)) + 4 * Real.pi * (K₁ * (Q * P)))
            = 6 / Real.pi * (K₁ * (Q * P)) + 2 * (K₁ * (Q * P)) := by
          field_simp
          ring
        have h6 : 6 / Real.pi ≤ 2 := by
          rw [div_le_iff₀ hpi]
          linarith only [Real.pi_gt_three]
        have hKQP : 0 ≤ K₁ * (Q * P) := by positivity
        calc _ ≤ (1 / (2 * Real.pi)) * (12 * (K₁ * (Q * P)) + 4 * Real.pi * (K₁ * (Q * P))) :=
              mul_le_mul_of_nonneg_left hsum3 hc
          _ = 6 / Real.pi * (K₁ * (Q * P)) + 2 * (K₁ * (Q * P)) := heq
          _ ≤ 2 * (K₁ * (Q * P)) + 2 * (K₁ * (Q * P)) := by gcongr
          _ = 4 * (K₁ * (Q * P)) := by ring
      have hQU : Q ≤ U ^ 10 := by
        rw [hQdef]
        exact pow_le_pow_right₀ (by linarith only [hU2]) (by norm_num)
      have hU10' : 1 ≤ U ^ 10 := one_le_pow₀ (by linarith only [hU2])
      have hQX : Q * P ≤ U ^ 10 * P := mul_le_mul_of_nonneg_right hQU hP0.le
      have hPX : P ≤ U ^ 10 * P := le_mul_of_one_le_left hP0.le hU10'
      have h3 : K₁ * (Q * P) ≤ K₁ * (U ^ 10 * P) := mul_le_mul_of_nonneg_left hQX hK₁0.le
      calc _ ≤ 3 * (U ^ 10 * P) + 3 * (U ^ 10 * P) + 4 * (K₁ * (U ^ 10 * P)) := by
            linarith only [hsplit, htr, hITn, he1, he2, hPX, h3]
        _ = K₂ * (U ^ 10 * P) := by rw [hK₂]; ring
    have hrhs : x * Real.exp (-(a / 2) * Real.log x ^ (1 / 10 : ℝ))
        = x * Real.exp (-(a / 2) * U) := by
      rw [hUdef, hLdef]
    rw [hrhs, mul_assoc]
    calc _ ≤ K₂ * (U ^ 10 * P) := hmain
      _ ≤ K₂ * (K₃ * (x * Real.exp (-(a / 2) * U))) :=
        mul_le_mul_of_nonneg_left hfinal hK₂0.le
  -- ## Part B: from `M₁` to `M` by differencing at `y = x * (1 + η)`
  obtain ⟨b, hb0, hb1, K, hK0, hM₁⟩ := hA
  refine ⟨b / 2, by positivity, ?_⟩
  refine IsBigO.of_bound (6 * K + 2) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1024)] with x hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hx0 : 0 < x := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  have hL : 1024 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1024) hx
    rwa [Real.log_exp, ← hLdef] at h
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = L ^ (1 / 10 : ℝ) := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := hUdef ▸ Real.rpow_nonneg (by linarith) _
  have hUL : U ≤ L := by
    rw [hUdef]
    calc L ^ (1 / 10 : ℝ) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = L := Real.rpow_one L
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.exp (-(b / 2) * U) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hη1 : η ≤ 1 := by
    rw [hηdef]
    exact Real.exp_le_one_iff.mpr (by nlinarith only [hb0, hU0])
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = x * η := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by
    rw [hWdef, hηdef]
    have hxe : x = Real.exp L := by rw [hLdef, Real.exp_log hx0]
    rw [hxe, ← Real.exp_add]
    exact Real.one_le_exp (by nlinarith only [hb1, hU0, hUL, hL])
  have hη2 : Real.exp (-b * U) = η * η := by
    rw [hηdef, ← Real.exp_add]; ring_nf
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = x * (1 + η) := ⟨_, rfl⟩
  have hxy : x ≤ y := by rw [hydef]; nlinarith only [hx0, hη0]
  have hy2 : y ≤ 2 * x := by rw [hydef]; nlinarith only [hx0, hη1]
  have hy0 : 0 < y := by linarith
  -- ## The two smoothed sums
  have hMx := hM₁ x hx
  have hMy := hM₁ y (le_trans hx hxy)
  rw [← hLdef, ← hUdef, hη2] at hMx
  have hlogy : L ≤ Real.log y := by rw [hLdef]; exact Real.log_le_log hx0 hxy
  have hUy : U ≤ Real.log y ^ (1 / 10 : ℝ) := by
    rw [hUdef]; exact Real.rpow_le_rpow (by linarith) hlogy (by norm_num)
  have hMy' : |∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n)| ≤ 2 * K * (W * η) := by
    refine hMy.trans ?_
    have he : Real.exp (-b * Real.log y ^ (1 / 10 : ℝ)) ≤ Real.exp (-b * U) :=
      Real.exp_le_exp.mpr (by nlinarith only [hUy, hb0])
    rw [hη2] at he
    calc K * (y * Real.exp (-b * Real.log y ^ (1 / 10 : ℝ)))
        ≤ K * (2 * x * (η * η)) := by gcongr
      _ = 2 * K * (W * η) := by rw [hWdef]; ring
  -- ## The differencing identity
  have hNM : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hIcc : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := by
    intro n; ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log (y / x) := ⟨_, rfl⟩
  have hident : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n))
      - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (x / n)
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ)) * ℓ
        + ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n) := by
    rw [hIcc, hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊x⌋₊) hNM, Finset.sum_mul]
    have hhead : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n))
        - ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (x / n)
        = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * ℓ := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by
        have := (Finset.mem_Ioc.mp hn).1
        exact_mod_cast this
      rw [hℓdef, Real.log_div hy0.ne' hn0.ne', Real.log_div hx0.ne' hn0.ne',
        Real.log_div hy0.ne' hx0.ne']
      ring
    linarith [hhead]
  -- ## The tail is at most `(W + 1) * ℓ`
  have hcard : (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℕ) : ℝ) ≤ W + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hNM]
    have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
    have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h3 : y - x = W := by rw [hydef, hWdef]; ring
    linarith
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef]; exact Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
  have htail : |∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n)| ≤ (W + 1) * ℓ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ℓ := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
          have hnx : x ≤ (n : ℝ) := by
            have hstep : ((⌊x⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn1
            have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
            linarith
          have hny : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn2) (Nat.floor_le hy0.le)
          have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hx0 hnx
          have hμ : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have hl0 : 0 ≤ Real.log (y / n) :=
            Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
          have hl1 : Real.log (y / n) ≤ ℓ := by
            rw [hℓdef]
            exact Real.log_le_log (div_pos hy0 hn0) (by gcongr)
          rw [abs_mul, abs_of_nonneg hl0]
          calc _ ≤ 1 * Real.log (y / n) := by gcongr
            _ ≤ ℓ := by linarith
      _ = (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℕ) : ℝ) * ℓ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (W + 1) * ℓ := by gcongr
  -- ## `η ≤ 2 ℓ`
  have hηℓ : η ≤ 2 * ℓ := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + η by linarith)
    have hyx : y / x = 1 + η := by rw [hydef]; field_simp
    rw [hℓdef, hyx]
    have h' : η / 2 ≤ 1 - (1 + η)⁻¹ := by
      rw [show 1 - (1 + η)⁻¹ = η / (1 + η) by field_simp; ring]
      exact div_le_div_of_nonneg_left hη0.le (by linarith) (by linarith)
    linarith
  have hℓpos : 0 < ℓ := by linarith
  -- ## Assembly
  have hMℓ : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ)| * ℓ
      ≤ (6 * K * W + W + 1) * ℓ := by
    rw [← abs_of_pos hℓpos, ← abs_mul, abs_of_pos hℓpos]
    have heq := hident
    have hab := abs_sub (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n))
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (x / n))
    have hsplit : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ)) * ℓ
        = ((∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n))
          - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (x / n))
          - ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log (y / n) := by
      rw [heq]; ring
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    have hWη : W * η ≤ W * (2 * ℓ) := mul_le_mul_of_nonneg_left hηℓ (by linarith)
    have hK1 : K * (W * η) ≤ K * (W * (2 * ℓ)) := mul_le_mul_of_nonneg_left hWη hK0.le
    have hKWℓ : 6 * K * W * ℓ = 3 * (K * (W * (2 * ℓ))) := by ring
    have hxW : K * (x * (η * η)) = K * (W * η) := by rw [hWdef]; ring
    have hexp : (6 * K * W + W + 1) * ℓ = 6 * K * W * ℓ + (W + 1) * ℓ := by ring
    linarith only [hab, hMx, hMy', htail, hK1, hKWℓ, hxW, hexp]
  have hM := le_of_mul_le_mul_right hMℓ hℓpos
  have hrhs : ‖x * Real.exp (-(b / 2) * Real.log x ^ (1 / 10 : ℝ))‖ = W := by
    rw [hWdef, hηdef, hUdef, hLdef, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, hrhs]
  nlinarith only [hM, hW1, hK0]

/-- **A bound for the Mertens function.** There is `c > 0` such that the Mertens function
`M(x) = ∑_{n ≤ x} μ(n)` satisfies `M(x) = O(x exp(-c (log x) ^ (1 / 10)))`. -/
theorem mertens_isBigO_mul_exp_neg_mul_log_rpow :
    ∃ c : ℝ, 0 < c ∧ (fun x : ℝ => (mertens x : ℝ))
      =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
  obtain ⟨c, hc, h⟩ := sum_moebius_isBigO_mul_exp_neg_mul_log_rpow
  refine ⟨c, hc, h.congr_left fun x => ?_⟩
  simp [mertens_apply]

end ArithmeticFunction

namespace Nat

/-- **Counting squarefree numbers.** The number of squarefree `n ≤ x` is
`6 x / π ^ 2 + O(√x)`. -/
theorem card_squarefree_sub_isBigO_sqrt :
    (fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter Squarefree).card : ℝ) - 6 / Real.pi ^ 2 * x)
      =O[atTop] fun x : ℝ => Real.sqrt x := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h := MetaMathlibExt.abs_card_hfree_sub_le 2 le_rfl x hx
  have hfilt : (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < 2) =
      (Finset.Icc 1 ⌊x⌋₊).filter Squarefree := by
    refine Finset.filter_congr fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [Nat.squarefree_iff_factorization_le_one hn0]
    constructor
    · intro h p
      by_cases hp : p ∈ n.primeFactors
      · have := h p hp
        omega
      · rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])]
        exact zero_le_one
    · intro h p _
      have := h p
      omega
  have hz : (riemannZeta ((2 : ℕ) : ℂ)).re = Real.pi ^ 2 / 6 := by
    rw [Nat.cast_ofNat, riemannZeta_two,
      show (Real.pi : ℂ) ^ 2 / 6 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have e : x / (Real.pi ^ 2 / 6) = 6 / Real.pi ^ 2 * x := by
    field_simp
  rw [hfilt, hz, e] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact h

/-- **Squarefree numbers with an even number of prime factors.** There is `c > 0` such that the
number of squarefree `n ≤ x` with an even number of prime factors is
`3 x / π ^ 2 + O(x exp(-c (log x) ^ (1 / 10)))`. -/
theorem card_squarefree_even_cardFactors_sub_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => Squarefree n ∧ Even (ArithmeticFunction.cardFactors n))).card : ℝ)
            - 3 / Real.pi ^ 2 * x)
        =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
  classical
  -- `E (x) = Q (x) / 2 + M (x) / 2`
  have hid : ∀ x : ℝ, ((((Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => Squarefree n ∧ Even (ArithmeticFunction.cardFactors n))).card : ℝ)
            - 3 / Real.pi ^ 2 * x)
        = (1 / 2) * ((((Finset.Icc 1 ⌊x⌋₊).filter Squarefree).card : ℝ)
            - 6 / Real.pi ^ 2 * x)
          + (1 / 2) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
    intro x
    rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum]
    have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (((if Squarefree n ∧ Even (ArithmeticFunction.cardFactors n) then 1 else 0 : ℕ)) : ℝ)
          = (1 / 2) * (((if Squarefree n then 1 else 0 : ℕ)) : ℝ)
            + (1 / 2) * ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
      intro n _
      by_cases h : Squarefree n
      · rw [ArithmeticFunction.moebius_apply_of_squarefree h, ite_eq_left h]
        rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with he | ho
        · rw [ite_eq_left ⟨h, he⟩, he.neg_one_pow]
          push_cast
          ring
        · rw [ite_eq_right (fun h' => (Nat.not_even_iff_odd.2 ho) h'.2), ho.neg_one_pow]
          push_cast
          ring
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h, ite_eq_right (fun h' => h h'.1),
          ite_eq_right h]
        simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  obtain ⟨c, hc, hM⟩ := ArithmeticFunction.sum_moebius_isBigO_mul_exp_neg_mul_log_rpow
  refine ⟨min c (1 / 2), lt_min hc (by norm_num), ?_⟩
  have hE : (fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) =O[atTop]
      fun x : ℝ => x * Real.exp (-min c (1 / 2) * Real.log x ^ (1 / 10 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hL : 0 ≤ Real.log x ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hx) _
    have hcc : min c (1 / 2) ≤ c := min_le_left _ _
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le),
      abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le), one_mul]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by linarith)
  have hR : (fun x : ℝ => Real.sqrt x) =O[atTop]
      fun x : ℝ => x * Real.exp (-min c (1 / 2) * Real.log x ^ (1 / 10 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
    rw [show Real.sqrt x = x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) by rw [Real.sqrt_eq_rpow]; norm_num]
    have hlog : 1 ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos 1) hx
      rwa [Real.log_exp] at this
    have hrp : Real.log x ^ (1 / 10 : ℝ) ≤ Real.log x := by
      calc Real.log x ^ (1 / 10 : ℝ) ≤ Real.log x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
        _ = Real.log x := Real.rpow_one _
    have hch : min c (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hL0 : 0 ≤ Real.log x ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
      abs_of_nonneg (mul_nonneg hx0.le (Real.exp_pos _).le), one_mul, Real.rpow_def_of_pos hx0]
    conv_rhs => rw [← Real.exp_log hx0]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    rw [Real.log_exp]
    nlinarith
  simp only [hid]
  exact IsBigO.add (IsBigO.const_mul_left (card_squarefree_sub_isBigO_sqrt.trans hR) _)
    (IsBigO.const_mul_left (hM.trans hE) _)

end Nat
