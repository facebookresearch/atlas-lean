/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Connected.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry16Corollary1JensenSeries

/-- Absolute summability of the Jensen-series terms. The key estimate is
`‖term k‖ ≤ C * q ^ k` with `q = |n| * exp (1 - n) < 1` on the range
`-ρ < n < 1` (using `ρ * exp (ρ + 1) = 1` at the left endpoint) and
`C = exp (‖x‖ / |n|)`; the case `n = 0` is the exponential series. -/
private lemma summable_jensen_series (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_eq : ρ * Real.exp (ρ + 1) = 1) (n : ℝ) (hn : -ρ < n ∧ n < 1) (x : ℂ) :
    Summable (fun k : ℕ => (x + (k : ℂ) * (n : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))) := by
  have hρ_lt_one : ρ < 1 := by
    by_contra h
    have h1ρ : (1 : ℝ) ≤ ρ := not_lt.mp h
    have hexp : Real.exp 2 ≤ Real.exp (ρ + 1) := Real.exp_le_exp.mpr (by linarith)
    have h3 : (3 : ℝ) ≤ Real.exp (ρ + 1) := by
      have h23 : (2 : ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
      linarith
    have hcon : (1 : ℝ) < ρ * Real.exp (ρ + 1) := by
      calc (1 : ℝ) < 1 * 3 := by norm_num
        _ ≤ ρ * Real.exp (ρ + 1) := mul_le_mul h1ρ h3 (by norm_num) hρ_pos.le
    linarith [hρ_eq]
  have hq_lt_one : |n| * Real.exp (1 - n) < 1 := by
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · have h1 : -n < ρ := by linarith [hn.1]
      have hn_neg : (0 : ℝ) < -n := neg_pos.mpr hn0
      have he : Real.exp (-n) < Real.exp ρ := Real.exp_lt_exp.mpr h1
      have hmul := mul_lt_mul'' h1 he hn_neg.le (Real.exp_pos _).le
      have hexp1 : Real.exp (1 - n) = Real.exp 1 * Real.exp (-n) := by
        rw [← Real.exp_add]; ring_nf
      rw [abs_of_neg hn0, hexp1]
      have e11 : Real.exp 1 * Real.exp ρ = Real.exp (ρ + 1) := by
        rw [← Real.exp_add]; ring_nf
      have h2 : Real.exp 1 * ((-n) * Real.exp (-n))
          < Real.exp 1 * (ρ * Real.exp ρ) :=
        mul_lt_mul_of_pos_left hmul (Real.exp_pos _)
      have h3 : Real.exp 1 * (ρ * Real.exp ρ) = ρ * Real.exp (ρ + 1) := by
        rw [← e11]; ring
      rw [h3, hρ_eq] at h2
      linarith [h2]
    · subst hn0
      simp
    · have hn1 : n ≠ 1 := ne_of_lt hn.2
      have hlog := Real.log_lt_sub_one_of_pos hn0 hn1
      have hexp : Real.exp (1 - n) < Real.exp (-Real.log n) :=
        Real.exp_lt_exp.mpr (by linarith)
      rw [Real.exp_neg, Real.exp_log hn0] at hexp
      rw [abs_of_pos hn0]
      have hfin := mul_lt_mul_of_pos_left hexp hn0
      rwa [mul_inv_cancel₀ (ne_of_gt hn0)] at hfin
  have hnorm : ∀ k : ℕ, ‖(x + (k : ℂ) * (n : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))‖
      = ‖x + (k : ℂ) * (n : ℂ)‖ ^ k / ((Nat.factorial k : ℝ) * Real.exp ((k : ℝ) * n)) := by
    intro k
    have hkn : (k : ℂ) * (n : ℂ) = (((k : ℝ) * n : ℝ) : ℂ) := by push_cast; ring
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hkn, Complex.norm_exp,
      Complex.ofReal_re]
  by_cases hn0 : n = 0
  · subst hn0
    have hfun : (fun k : ℕ => (x + (k : ℂ) * (((0 : ℝ)) : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (((0 : ℝ)) : ℂ))))
        = (fun k : ℕ => x ^ k / ((Nat.factorial k : ℂ))) := by
      funext k
      simp
    rw [hfun]
    apply Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖x‖)
    intro k
    rw [norm_div, norm_pow, Complex.norm_natCast]
  · have habs : 0 < |n| := abs_pos.mpr hn0
    have habsne : |n| ≠ 0 := ne_of_gt habs
    set C : ℝ := Real.exp (‖x‖ / |n|) with hC
    have hC1 : 1 ≤ C := Real.one_le_exp (div_nonneg (norm_nonneg _) habs.le)
    have hqnn : 0 ≤ |n| * Real.exp (1 - n) :=
      mul_nonneg habs.le (Real.exp_pos _).le
    have hbound : ∀ k : ℕ, ‖(x + (k : ℂ) * (n : ℂ)) ^ k /
          ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))‖
        ≤ C * (|n| * Real.exp (1 - n)) ^ k := by
      intro k
      rw [hnorm k]
      by_cases hk : k = 0
      · subst hk
        simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero,
          zero_mul, add_zero, Real.exp_zero, div_one]
        exact hC1
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hkr : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
        have hkrne : (k : ℝ) ≠ 0 := ne_of_gt hkr
        have hD : (0 : ℝ) < (Nat.factorial k : ℝ) * Real.exp ((k : ℝ) * n) :=
          mul_pos (by exact_mod_cast Nat.factorial_pos k) (Real.exp_pos _)
        have h1 : ‖x + (k : ℂ) * (n : ℂ)‖ ≤ ‖x‖ + (k : ℝ) * |n| := by
          have hle := norm_add_le x ((k : ℂ) * (n : ℂ))
          refine le_trans hle ?_
          rw [norm_mul, norm_natCast, Complex.norm_real, Real.norm_eq_abs]
        have hkk : ((k : ℝ)) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (k : ℝ) :=
          Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg _) _
        have kk : (k : ℝ) * (‖x‖ / (k : ℝ)) = ‖x‖ := by
          field_simp
        have e5 : ‖x‖ + (k : ℝ) * |n| = (k : ℝ) * (|n| + ‖x‖ / (k : ℝ)) := by
          rw [mul_add, kk, add_comm]
        have h2 : (1 + (‖x‖ / |n|) / (k : ℝ)) ^ k ≤ Real.exp (‖x‖ / |n|) := by
          have hle : (1 + (‖x‖ / |n|) / (k : ℝ)) ≤ Real.exp ((‖x‖ / |n|) / (k : ℝ)) := by
            have hh := Real.add_one_le_exp ((‖x‖ / |n|) / (k : ℝ)); linarith
          have h3 := pow_le_pow_left₀ (by positivity) hle k
          rw [← Real.exp_nat_mul] at h3
          have e4 : (k : ℝ) * ((‖x‖ / |n|) / (k : ℝ)) = ‖x‖ / |n| := by
            field_simp
          rwa [e4] at h3
        have hfac : |n| + ‖x‖ / (k : ℝ) = |n| * (1 + (‖x‖ / |n|) / (k : ℝ)) := by
          field_simp
        have e6 : (|n| + ‖x‖ / (k : ℝ)) ^ k
            = |n| ^ k * (1 + (‖x‖ / |n|) / (k : ℝ)) ^ k := by
          rw [hfac, mul_pow]
        have hstep1 : ‖x + (k : ℂ) * (n : ℂ)‖ ^ k
            ≤ ((k : ℝ)) ^ k * (|n| + ‖x‖ / (k : ℝ)) ^ k := by
          calc ‖x + (k : ℂ) * (n : ℂ)‖ ^ k ≤ (‖x‖ + (k : ℝ) * |n|) ^ k :=
                pow_le_pow_left₀ (norm_nonneg _) h1 k
            _ = ((k : ℝ)) ^ k * (|n| + ‖x‖ / (k : ℝ)) ^ k := by rw [e5, mul_pow]
        have hstep2 : ((k : ℝ)) ^ k * (|n| + ‖x‖ / (k : ℝ)) ^ k / (Nat.factorial k : ℝ)
            ≤ Real.exp (k : ℝ) * (|n| + ‖x‖ / (k : ℝ)) ^ k := by
          have heq : ((k : ℝ)) ^ k * (|n| + ‖x‖ / (k : ℝ)) ^ k / (Nat.factorial k : ℝ)
              = (((k : ℝ)) ^ k / (Nat.factorial k : ℝ)) * (|n| + ‖x‖ / (k : ℝ)) ^ k := by
            ring
          rw [heq]
          exact mul_le_mul_of_nonneg_right hkk (pow_nonneg (by positivity) _)
        have hexp_eq : Real.exp (k : ℝ) / Real.exp ((k : ℝ) * n)
            = (Real.exp (1 - n)) ^ k := by
          rw [← Real.exp_sub, ← Real.exp_nat_mul]
          congr 1
          ring
        have hstep3 : Real.exp (k : ℝ) * (|n| + ‖x‖ / (k : ℝ)) ^ k
            / Real.exp ((k : ℝ) * n) ≤ C * (|n| * Real.exp (1 - n)) ^ k := by
          rw [e6, hC, mul_pow]
          have hpos1 : (0 : ℝ) ≤ |n| ^ k := pow_nonneg habs.le _
          calc Real.exp (k : ℝ) * (|n| ^ k * (1 + (‖x‖ / |n|) / (k : ℝ)) ^ k)
                / Real.exp ((k : ℝ) * n)
              = (Real.exp (k : ℝ) / Real.exp ((k : ℝ) * n))
                * (|n| ^ k * (1 + (‖x‖ / |n|) / (k : ℝ)) ^ k) := by ring
            _ = (Real.exp (1 - n)) ^ k * (|n| ^ k * (1 + (‖x‖ / |n|) / (k : ℝ)) ^ k) := by
                rw [hexp_eq]
            _ ≤ (Real.exp (1 - n)) ^ k * (|n| ^ k * Real.exp (‖x‖ / |n|)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left h2 hpos1) (pow_nonneg (Real.exp_pos _).le _)
            _ = Real.exp (‖x‖ / |n|) * (|n| ^ k * (Real.exp (1 - n)) ^ k) := by ring
        calc ‖x + (k : ℂ) * (n : ℂ)‖ ^ k / ((Nat.factorial k : ℝ) * Real.exp ((k : ℝ) * n))
            = (‖x + (k : ℂ) * (n : ℂ)‖ ^ k / (Nat.factorial k : ℝ))
              / Real.exp ((k : ℝ) * n) := by ring
          _ ≤ ((((k : ℝ)) ^ k * (|n| + ‖x‖ / (k : ℝ)) ^ k) / (Nat.factorial k : ℝ))
              / Real.exp ((k : ℝ) * n) :=
              div_le_div_of_nonneg_right
                (div_le_div_of_nonneg_right hstep1
                  (by exact_mod_cast (Nat.factorial_pos k).le))
                (Real.exp_pos _).le
          _ ≤ (Real.exp (k : ℝ) * (|n| + ‖x‖ / (k : ℝ)) ^ k) / Real.exp ((k : ℝ) * n) :=
              div_le_div_of_nonneg_right hstep2 (Real.exp_pos _).le
          _ ≤ C * (|n| * Real.exp (1 - n)) ^ k := hstep3
    have hgeom := summable_geometric_of_norm_lt_one
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hqnn])
    exact Summable.of_norm_bounded (hgeom.mul_left C) hbound

/-- The Jensen series at `n = 0` is the exponential series. -/
private lemma jensen_series_zero (x : ℂ) :
    HasSum (fun k : ℕ => (x + (k : ℂ) * (((0 : ℝ)) : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (((0 : ℝ)) : ℂ))))
      (Complex.exp x / (1 - (((0 : ℝ)) : ℂ))) := by
  have hfun : (fun k : ℕ => (x + (k : ℂ) * (((0 : ℝ)) : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (((0 : ℝ)) : ℂ))))
      = (fun k : ℕ => x ^ k / ((Nat.factorial k : ℂ))) := by
    funext k
    simp
  have hval : Complex.exp x / (1 - (((0 : ℝ)) : ℂ)) = NormedSpace.exp x := by
    simp [Complex.exp_eq_exp_ℂ]
  rw [hfun, hval]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- Alternating binomial moment of falling factorials. -/
private lemma choose_descFactorial_sum (N j : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
        ((N.choose k : ℕ) : ℂ) * (-1 : ℂ) ^ k *
          ((Nat.descFactorial k j : ℕ) : ℂ)
      = if j = N then (-1 : ℂ) ^ N * (Nat.factorial N : ℂ) else 0 := by
  have hdesc : ∀ k : ℕ, ((Nat.descFactorial k j : ℕ) : ℂ)
      = (Nat.factorial j : ℂ) * ((Nat.choose k j : ℕ) : ℂ) := by
    intro k
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hfactor : ∀ k : ℕ, ((N.choose k : ℕ) : ℂ) * (-1 : ℂ) ^ k *
        ((Nat.descFactorial k j : ℕ) : ℂ)
      = (Nat.factorial j : ℂ) * (((N.choose k : ℕ) : ℂ) *
        ((Nat.choose k j : ℕ) : ℂ) * (-1 : ℂ) ^ k) := by
    intro k
    rw [hdesc k]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hfactor k)]
  rw [← Finset.mul_sum]
  have hinner : ∑ k ∈ Finset.range (N + 1),
        ((N.choose k : ℕ) : ℂ) * ((Nat.choose k j : ℕ) : ℂ) * (-1 : ℂ) ^ k
      = ((N.choose j : ℕ) : ℂ) * (-1 : ℂ) ^ j * (0 : ℂ) ^ (N - j) := by
    by_cases hjN : j ≤ N
    · have hsub : Finset.Ico j (N + 1) ⊆ Finset.range (N + 1) := by
        intro k hk
        simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
        omega
      have hzero : ∀ k ∈ Finset.range (N + 1),
          k ∉ Finset.Ico j (N + 1) →
          ((N.choose k : ℕ) : ℂ) * ((Nat.choose k j : ℕ) : ℂ) *
            (-1 : ℂ) ^ k = 0 := by
        intro k hk_mem hk
        simp only [Finset.mem_range] at hk_mem
        simp only [Finset.mem_Ico, not_and_or] at hk
        have hkj : k < j := by
          rcases hk with hk | hk
          · omega
          · omega
        rw [Nat.choose_eq_zero_of_lt hkj]
        simp
      rw [← Finset.sum_subset hsub hzero]
      rw [Finset.sum_Ico_eq_sum_range]
      have hterm : ∀ t ∈ Finset.range (N + 1 - j),
          ((N.choose (j + t) : ℕ) : ℂ) * ((Nat.choose (j + t) j : ℕ) : ℂ) *
            (-1 : ℂ) ^ (j + t)
          = ((N.choose j : ℕ) : ℂ) * (-1 : ℂ) ^ j *
            (((Nat.choose (N - j) t : ℕ) : ℂ) * (-1 : ℂ) ^ t) := by
        intro t _
        have hcm : N.choose (j + t) * (j + t).choose j
            = N.choose j * (N - j).choose ((j + t) - j) :=
          Nat.choose_mul (Nat.le_add_right j t)
        have hsub2 : (j + t) - j = t := by omega
        rw [hsub2] at hcm
        have hcmC : ((N.choose (j + t) : ℕ) : ℂ) *
              ((Nat.choose (j + t) j : ℕ) : ℂ)
            = ((N.choose j : ℕ) : ℂ) * ((Nat.choose (N - j) t : ℕ) : ℂ) := by
          exact_mod_cast hcm
        rw [pow_add, hcmC]
        ring
      rw [Finset.sum_congr rfl hterm]
      rw [← Finset.mul_sum]
      congr 1
      have hpow : ((-1 : ℂ) + 1) ^ (N - j)
          = ∑ t ∈ Finset.range (N - j + 1),
            ((Nat.choose (N - j) t : ℕ) : ℂ) * (-1 : ℂ) ^ t := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro t _
        simp [mul_comm]
      have h01 : ((-1 : ℂ) + 1) ^ (N - j) = (0 : ℂ) ^ (N - j) := by
        congr 1
        ring
      rw [h01] at hpow
      have hlen : N + 1 - j = N - j + 1 := by omega
      rw [hlen]
      exact hpow.symm
    · push Not at hjN
      have h1 : ∀ k ∈ Finset.range (N + 1),
          ((N.choose k : ℕ) : ℂ) * ((Nat.choose k j : ℕ) : ℂ) *
            (-1 : ℂ) ^ k = 0 := by
        intro k hk
        simp only [Finset.mem_range] at hk
        have hkj : k < j := by omega
        rw [Nat.choose_eq_zero_of_lt hkj]
        simp
      rw [Finset.sum_eq_zero h1]
      have h2 : N.choose j = 0 := Nat.choose_eq_zero_of_lt hjN
      rw [h2]
      simp
  rw [hinner]
  by_cases hj : j = N
  · subst hj
    simp only [ite_true, Nat.sub_self, pow_zero, mul_one,
      Nat.choose_self, Nat.cast_one, one_mul]
    ring
  · simp only [hj, ite_false]
    by_cases hjN : j ≤ N
    · have hsub : N - j ≠ 0 := by omega
      rw [zero_pow hsub]
      ring
    · push Not at hjN
      have h2 : N.choose j = 0 := Nat.choose_eq_zero_of_lt hjN
      rw [h2]
      simp

/-- Finite difference of monomials via Stirling numbers. -/
private lemma finite_diff_pow (N : ℕ) (y n : ℂ) :
    ∑ k ∈ Finset.range (N + 1),
        ((N.choose k : ℕ) : ℂ) * (-1 : ℂ) ^ k * (y - (k : ℂ) * n) ^ N
      = (Nat.factorial N : ℂ) * n ^ N := by
  have hexpand : ∀ k : ℕ, (y - (k : ℂ) * n) ^ N
      = ∑ m ∈ Finset.range (N + 1),
        ((N.choose m : ℕ) : ℂ) * y ^ (N - m) * ((-n) ^ m * (k : ℂ) ^ m) := by
    intro k
    have hbin : (y + (-(k : ℂ) * n)) ^ N
        = ∑ m ∈ Finset.range (N + 1),
          (y ^ (N - m) * (-(k : ℂ) * n) ^ m *
            ((N.choose m : ℕ) : ℂ)) := by
      rw [add_comm y _, add_pow]
      apply Finset.sum_congr rfl
      intro m _
      ring
    have hsub : y - (k : ℂ) * n = y + (-(k : ℂ) * n) := by ring
    rw [hsub, hbin]
    apply Finset.sum_congr rfl
    intro m _
    have hkn : (-(k : ℂ) * n) ^ m = (-n) ^ m * (k : ℂ) ^ m := by
      have hneg : (-(k : ℂ) * n) = (k : ℂ) * (-n) := by ring
      rw [hneg, mul_pow]
      ring
    rw [hkn]
    ring
  have hstir : ∀ (k m : ℕ), (k : ℂ) ^ m
      = ∑ j ∈ Finset.range (m + 1),
        ((Nat.stirlingSecond m j : ℕ) : ℂ) *
          ((Nat.descFactorial k j : ℕ) : ℂ) := by
    intro k m
    have hnat := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k m
    have hcast : ((k ^ m : ℕ) : ℂ)
        = ∑ j ∈ Finset.range (m + 1),
          ((Nat.stirlingSecond m j : ℕ) : ℂ) *
            ((Nat.descFactorial k j : ℕ) : ℂ) := by
      rw [hnat]
      push_cast
      rfl
    simpa using hcast
  have hmain : ∑ k ∈ Finset.range (N + 1),
        ((N.choose k : ℕ) : ℂ) * (-1 : ℂ) ^ k * (y - (k : ℂ) * n) ^ N
      = ∑ m ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ((N.choose m : ℕ) : ℂ) * y ^ (N - m) * (-n) ^ m *
          ((Nat.stirlingSecond m j : ℕ) : ℂ) *
          (∑ k ∈ Finset.range (N + 1),
            ((N.choose k : ℕ) : ℂ) * (-1 : ℂ) ^ k *
              ((Nat.descFactorial k j : ℕ) : ℂ)) := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [hexpand k])]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_range] at hm
    have hjext : ∀ k : ℕ, ∑ j ∈ Finset.range (m + 1),
          ((Nat.stirlingSecond m j : ℕ) : ℂ) *
            ((Nat.descFactorial k j : ℕ) : ℂ)
        = ∑ j ∈ Finset.range (N + 1),
          ((Nat.stirlingSecond m j : ℕ) : ℂ) *
            ((Nat.descFactorial k j : ℕ) : ℂ) := by
      intro k
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hjm
      simp only [Finset.mem_range] at hjm
      push Not at hjm
      have hmj : m < j := by omega
      rw [Nat.stirlingSecond_eq_zero_of_lt hmj]
      simp
    simp only [hstir] at ⊢
    rw [Finset.sum_congr rfl (fun k _ => by rw [hjext k])]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hmain]
  have hsingle : ∑ m ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ((N.choose m : ℕ) : ℂ) * y ^ (N - m) * (-n) ^ m *
          ((Nat.stirlingSecond m j : ℕ) : ℂ) *
          (∑ k ∈ Finset.range (N + 1),
            ((N.choose k : ℕ) : ℂ) * (-1 : ℂ) ^ k *
              ((Nat.descFactorial k j : ℕ) : ℂ))
      = (Nat.factorial N : ℂ) * n ^ N := by
    rw [Finset.sum_eq_single N]
    · rw [Finset.sum_eq_single N]
      · simp only [Nat.choose_self, Nat.cast_one, one_mul, mul_one,
          Nat.sub_self, pow_zero, Nat.stirlingSecond_self]
        rw [choose_descFactorial_sum]
        simp only [ite_true]
        have hpow : (-n) ^ N * ((-1 : ℂ) ^ N * (Nat.factorial N : ℂ))
            = (Nat.factorial N : ℂ) * n ^ N := by
          rw [← mul_assoc, ← mul_pow]
          have hneg : (-n) * (-1 : ℂ) = n := by ring
          rw [hneg]
          ring
        exact hpow
      · intro j _ hjN
        rw [choose_descFactorial_sum]
        simp only [hjN, ite_false, mul_zero]
      · intro hjmem
        simp only [Finset.mem_range] at hjmem
        push Not at hjmem
        omega
    · intro m hm_mem hmN
      simp only [Finset.mem_range] at hm_mem
      apply Finset.sum_eq_zero
      intro j _
      by_cases hjN : j = N
      · rw [hjN]
        have hmN2 : m < N := by omega
        rw [Nat.stirlingSecond_eq_zero_of_lt hmN2]
        simp
      · rw [choose_descFactorial_sum]
        simp only [hjN, ite_false, mul_zero]
    · intro hmem
      simp only [Finset.mem_range] at hmem
      push Not at hmem
      omega
  exact hsingle

/-- Descending factorial scaling. -/
private lemma descFactorial_succ_mul (N j : ℕ) :
    Nat.descFactorial (N + 1) (j + 1) = (N + 1) * Nat.descFactorial N j := by
  induction j generalizing N with
  | zero =>
    simp [Nat.descFactorial]
  | succ j ih =>
    have h1 : Nat.descFactorial (N + 1) (j + 1 + 1)
        = ((N + 1) - (j + 1)) * Nat.descFactorial (N + 1) (j + 1) :=
      Nat.descFactorial_succ (N + 1) (j + 1)
    have h2 : Nat.descFactorial N (j + 1)
        = (N - j) * Nat.descFactorial N j :=
      Nat.descFactorial_succ N j
    rw [h1, ih]
    have hsub : (N + 1) - (j + 1) = N - j := by omega
    rw [hsub, h2]
    ring

/-- Finite Jensen sum identity. -/
private lemma finite_jensen_sum (N : ℕ) (x y n : ℂ) :
    ∑ k ∈ Finset.range (N + 1),
        ((N.choose k : ℕ) : ℂ) * (x + (k : ℂ) * n) ^ k * (y - (k : ℂ) * n) ^ (N - k)
      = ∑ j ∈ Finset.range (N + 1),
        ((Nat.descFactorial N j : ℕ) : ℂ) * n ^ j * (x + y) ^ (N - j) := by
  induction N generalizing x y n with
  | zero =>
    simp
  | succ N ih =>
    have hLpos : ∀ X : ℂ, HasDerivAt
        (fun X' : ℂ => ∑ k ∈ Finset.range (N + 1 + 1),
          ((Nat.choose (N + 1) k : ℕ) : ℂ) * (X' + (k : ℂ) * n) ^ k *
            (y - (k : ℂ) * n) ^ (N + 1 - k))
        (∑ k ∈ Finset.range (N + 1 + 1),
          ((Nat.choose (N + 1) k : ℕ) : ℂ) * ((k : ℂ) * (X + (k : ℂ) * n) ^ (k - 1)) *
            (y - (k : ℂ) * n) ^ (N + 1 - k)) X := by
      intro X
      apply HasDerivAt.fun_sum
      intro k _
      have hbase : HasDerivAt (fun X' : ℂ => X' + (k : ℂ) * n) 1 X :=
        (hasDerivAt_id X).add_const ((k : ℂ) * n)
      have hpow : HasDerivAt (fun X' : ℂ => (X' + (k : ℂ) * n) ^ k)
          ((k : ℂ) * (X + (k : ℂ) * n) ^ (k - 1) * 1) X :=
        hbase.pow k
      have hmul := hpow.const_mul
        (((Nat.choose (N + 1) k : ℕ) : ℂ) * (y - (k : ℂ) * n) ^ (N + 1 - k))
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
    have hRpos : ∀ X : ℂ, HasDerivAt
        (fun X' : ℂ => ∑ j ∈ Finset.range (N + 1 + 1),
          ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (X' + y) ^ (N + 1 - j))
        (∑ j ∈ Finset.range (N + 1 + 1),
          ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j *
            (((N + 1 - j : ℕ) : ℂ) * (X + y) ^ (N + 1 - j - 1))) X := by
      intro X
      apply HasDerivAt.fun_sum
      intro j _
      have hbase : HasDerivAt (fun X' : ℂ => X' + y) 1 X :=
        (hasDerivAt_id X).add_const y
      have hpow : HasDerivAt (fun X' : ℂ => (X' + y) ^ (N + 1 - j))
          (((N + 1 - j : ℕ) : ℂ) * (X + y) ^ (N + 1 - j - 1) * 1) X :=
        hbase.pow (N + 1 - j)
      have hmul := hpow.const_mul
        (((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
    have hderivL : ∀ X : ℂ, deriv
        (fun X' : ℂ => ∑ k ∈ Finset.range (N + 1 + 1),
          ((Nat.choose (N + 1) k : ℕ) : ℂ) * (X' + (k : ℂ) * n) ^ k *
            (y - (k : ℂ) * n) ^ (N + 1 - k)) X
        = ((N + 1 : ℕ) : ℂ) * ∑ j ∈ Finset.range (N + 1),
          ((N.choose j : ℕ) : ℂ) * ((X + n) + (j : ℂ) * n) ^ j *
            ((y - n) - (j : ℂ) * n) ^ (N - j) := by
      intro X
      rw [(hLpos X).deriv]
      have hsplit : ∑ k ∈ Finset.range (N + 1 + 1),
            ((Nat.choose (N + 1) k : ℕ) : ℂ) * ((k : ℂ) * (X + (k : ℂ) * n) ^ (k - 1)) *
              (y - (k : ℂ) * n) ^ (N + 1 - k)
          = ∑ j ∈ Finset.range (N + 1),
            (((N + 1 : ℕ) : ℂ) * ((N.choose j : ℕ) : ℂ)) *
              ((X + n) + (j : ℂ) * n) ^ j * ((y - n) - (j : ℂ) * n) ^ (N - j) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero,
          zero_mul, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j _
        have hNat : ((Nat.choose (N + 1) (j + 1) : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ)
            = ((N + 1 : ℕ) : ℂ) * ((N.choose j : ℕ) : ℂ) := by
          have h := Nat.add_one_mul_choose_eq N j
          have hcast : (((N + 1) * N.choose j : ℕ) : ℂ)
              = ((Nat.choose (N + 1) (j + 1) : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) := by
            exact_mod_cast h
          push_cast at hcast ⊢
          exact hcast.symm
        have hX : (X + ((j + 1 : ℕ) : ℂ) * n) ^ ((j + 1) - 1)
            = ((X + n) + (j : ℂ) * n) ^ j := by
          have hj1 : ((j + 1 : ℕ) : ℂ) = (j : ℂ) + 1 := by push_cast; ring
          rw [hj1]
          have hjsub : j + 1 - 1 = j := by omega
          rw [hjsub]
          congr 1
          ring
        have hY : (y - ((j + 1 : ℕ) : ℂ) * n) ^ (N + 1 - (j + 1))
            = ((y - n) - (j : ℂ) * n) ^ (N - j) := by
          have hj1 : ((j + 1 : ℕ) : ℂ) = (j : ℂ) + 1 := by push_cast; ring
          rw [hj1]
          have hsub : N + 1 - (j + 1) = N - j := by omega
          rw [hsub]
          congr 1
          ring
        have hsub2 : j + 1 - 1 = j := by omega
        simp only [hsub2] at hX ⊢
        rw [hX, hY]
        linear_combination
          (((X + n) + (j : ℂ) * n) ^ j * (((y - n) - (j : ℂ) * n) ^ (N - j))) * hNat
      rw [hsplit]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
    have hderivR : ∀ X : ℂ, deriv
        (fun X' : ℂ => ∑ j ∈ Finset.range (N + 1 + 1),
          ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (X' + y) ^ (N + 1 - j)) X
        = ((N + 1 : ℕ) : ℂ) * ∑ i ∈ Finset.range (N + 1),
          ((Nat.descFactorial N i : ℕ) : ℂ) * n ^ i * (X + y) ^ (N - i) := by
      intro X
      rw [(hRpos X).deriv]
      have hsplitR : ∑ j ∈ Finset.range (N + 1 + 1),
            ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j *
              (((N + 1 - j : ℕ) : ℂ) * (X + y) ^ (N + 1 - j - 1))
          = ∑ i ∈ Finset.range (N + 1),
            (((N + 1 : ℕ) : ℂ) * ((Nat.descFactorial N i : ℕ) : ℂ)) *
              n ^ i * (X + y) ^ (N - i) := by
        rw [Finset.sum_range_succ]
        have hlast : ((Nat.descFactorial (N + 1) (N + 1) : ℕ) : ℂ) * n ^ (N + 1) *
              (((N + 1 - (N + 1) : ℕ) : ℂ) * (X + y) ^ (N + 1 - (N + 1) - 1)) = 0 := by
          simp
        rw [hlast, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_range] at hj
        have hjN : j ≤ N := by omega
        have hdesc : ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * ((N + 1 - j : ℕ) : ℂ)
            = ((N + 1 : ℕ) : ℂ) * ((Nat.descFactorial N j : ℕ) : ℂ) := by
          have h1 : Nat.descFactorial (N + 1) (j + 1)
              = ((N + 1) - j) * Nat.descFactorial (N + 1) j :=
            Nat.descFactorial_succ (N + 1) j
          have h2 : Nat.descFactorial (N + 1) (j + 1)
              = (N + 1) * Nat.descFactorial N j :=
            descFactorial_succ_mul N j
          have h3 : (N + 1 - j : ℕ) * Nat.descFactorial (N + 1) j
              = (N + 1) * Nat.descFactorial N j := by
            rw [← h1, h2]
          have hcast : (((N + 1 - j : ℕ) * Nat.descFactorial (N + 1) j : ℕ) : ℂ)
              = (((N + 1 : ℕ) * Nat.descFactorial N j : ℕ) : ℂ) := by
            exact_mod_cast h3
          push_cast at hcast ⊢
          linear_combination hcast
        have hsub : N + 1 - j - 1 = N - j := by omega
        rw [hsub]
        linear_combination (n ^ j * (X + y) ^ (N - j)) * hdesc
      rw [hsplitR]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
    have hbaseL : ∑ k ∈ Finset.range (N + 1 + 1),
          ((Nat.choose (N + 1) k : ℕ) : ℂ) * ((-y) + (k : ℂ) * n) ^ k *
            (y - (k : ℂ) * n) ^ (N + 1 - k)
        = ((Nat.factorial (N + 1) : ℕ) : ℂ) * n ^ (N + 1) := by
      have hterm : ∀ k ∈ Finset.range (N + 1 + 1),
          ((Nat.choose (N + 1) k : ℕ) : ℂ) * ((-y) + (k : ℂ) * n) ^ k *
            (y - (k : ℂ) * n) ^ (N + 1 - k)
          = ((Nat.choose (N + 1) k : ℕ) : ℂ) * (-1 : ℂ) ^ k *
            (y - (k : ℂ) * n) ^ (N + 1) := by
        intro k hk
        simp only [Finset.mem_range] at hk
        have hkN : k ≤ N + 1 := by omega
        have hneg : (-y) + (k : ℂ) * n = - (y - (k : ℂ) * n) := by ring
        rw [hneg, neg_pow]
        have hadd : k + (N + 1 - k) = N + 1 := by omega
        have hpow : (y - (k : ℂ) * n) ^ k * (y - (k : ℂ) * n) ^ (N + 1 - k)
            = (y - (k : ℂ) * n) ^ (N + 1) := by
          rw [← pow_add, hadd]
        linear_combination
          (((Nat.choose (N + 1) k : ℕ) : ℂ) * (-1 : ℂ) ^ k) * hpow
      rw [Finset.sum_congr rfl hterm]
      exact finite_diff_pow (N + 1) y n
    have hbaseR : ∑ j ∈ Finset.range (N + 1 + 1),
          ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * ((-y) + y) ^ (N + 1 - j)
        = ((Nat.factorial (N + 1) : ℕ) : ℂ) * n ^ (N + 1) := by
      have h0 : (-y) + y = (0 : ℂ) := by ring
      rw [Finset.sum_congr rfl (fun j _ => by rw [h0])]
      rw [Finset.sum_eq_single (N + 1)]
      · simp only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
      · intro j hj_mem hjN
        simp only [Finset.mem_range] at hj_mem
        have hjN2 : j < N + 1 := by omega
        have hpos : N + 1 - j ≠ 0 := by omega
        rw [zero_pow hpos]
        ring
      · intro hmem
        simp only [Finset.mem_range] at hmem
        exact absurd hmem (by omega)
    have hdiff : Differentiable ℂ
        (fun X' : ℂ => (∑ k ∈ Finset.range (N + 1 + 1),
            ((Nat.choose (N + 1) k : ℕ) : ℂ) * (X' + (k : ℂ) * n) ^ k *
              (y - (k : ℂ) * n) ^ (N + 1 - k))
          - ∑ j ∈ Finset.range (N + 1 + 1),
            ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (X' + y) ^ (N + 1 - j)) := by
      apply Differentiable.sub
      · exact fun X => (hLpos X).differentiableAt
      · exact fun X => (hRpos X).differentiableAt
    have hderiv0 : ∀ X : ℂ, deriv
        (fun X' : ℂ => (∑ k ∈ Finset.range (N + 1 + 1),
            ((Nat.choose (N + 1) k : ℕ) : ℂ) * (X' + (k : ℂ) * n) ^ k *
              (y - (k : ℂ) * n) ^ (N + 1 - k))
          - ∑ j ∈ Finset.range (N + 1 + 1),
            ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (X' + y) ^ (N + 1 - j)) X
        = 0 := by
      intro X
      have hLdiff : DifferentiableAt ℂ
          (fun X' : ℂ => ∑ k ∈ Finset.range (N + 1 + 1),
            ((Nat.choose (N + 1) k : ℕ) : ℂ) * (X' + (k : ℂ) * n) ^ k *
              (y - (k : ℂ) * n) ^ (N + 1 - k)) X :=
        (hLpos X).differentiableAt
      have hRdiff : DifferentiableAt ℂ
          (fun X' : ℂ => ∑ j ∈ Finset.range (N + 1 + 1),
            ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (X' + y) ^ (N + 1 - j)) X :=
        (hRpos X).differentiableAt
      rw [deriv_fun_sub hLdiff hRdiff, hderivL X, hderivR X]
      have hIH : ∑ j ∈ Finset.range (N + 1),
            ((N.choose j : ℕ) : ℂ) * ((X + n) + (j : ℂ) * n) ^ j *
              ((y - n) - (j : ℂ) * n) ^ (N - j)
          = ∑ i ∈ Finset.range (N + 1),
            ((Nat.descFactorial N i : ℕ) : ℂ) * n ^ i * (X + y) ^ (N - i) := by
        have h1 := ih (X + n) (y - n) n
        have h2 : ∀ i ∈ Finset.range (N + 1),
            ((Nat.descFactorial N i : ℕ) : ℂ) * n ^ i * ((X + n) + (y - n)) ^ (N - i)
            = ((Nat.descFactorial N i : ℕ) : ℂ) * n ^ i * (X + y) ^ (N - i) := by
          intro i _
          have hxy : (X + n) + (y - n) = X + y := by ring
          rw [hxy]
        rw [Finset.sum_congr rfl h2] at h1
        exact h1
      rw [hIH]
      ring
    have hconst := is_const_of_deriv_eq_zero hdiff hderiv0 x (-y)
    have hbase0 : (∑ k ∈ Finset.range (N + 1 + 1),
            ((Nat.choose (N + 1) k : ℕ) : ℂ) * ((-y) + (k : ℂ) * n) ^ k *
              (y - (k : ℂ) * n) ^ (N + 1 - k))
          - ∑ j ∈ Finset.range (N + 1 + 1),
            ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * ((-y) + y) ^ (N + 1 - j)
        = 0 := by
      rw [hbaseL, hbaseR]
      ring
    have hconcl : (∑ k ∈ Finset.range (N + 1 + 1),
            ((Nat.choose (N + 1) k : ℕ) : ℂ) * (x + (k : ℂ) * n) ^ k *
              (y - (k : ℂ) * n) ^ (N + 1 - k))
          - ∑ j ∈ Finset.range (N + 1 + 1),
            ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (x + y) ^ (N + 1 - j)
        = 0 := by
      have hfx : (fun X' : ℂ => (∑ k ∈ Finset.range (N + 1 + 1),
              ((Nat.choose (N + 1) k : ℕ) : ℂ) * (X' + (k : ℂ) * n) ^ k *
                (y - (k : ℂ) * n) ^ (N + 1 - k))
            - ∑ j ∈ Finset.range (N + 1 + 1),
              ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (X' + y) ^ (N + 1 - j)) x
          = (fun X' : ℂ => (∑ k ∈ Finset.range (N + 1 + 1),
              ((Nat.choose (N + 1) k : ℕ) : ℂ) * (X' + (k : ℂ) * n) ^ k *
                (y - (k : ℂ) * n) ^ (N + 1 - k))
            - ∑ j ∈ Finset.range (N + 1 + 1),
              ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (X' + y) ^ (N + 1 - j)) (-y) :=
        hconst
      simpa using hfx.trans hbase0
    have hfinal : ∑ k ∈ Finset.range (N + 1 + 1),
          ((Nat.choose (N + 1) k : ℕ) : ℂ) * (x + (k : ℂ) * n) ^ k *
            (y - (k : ℂ) * n) ^ (N + 1 - k)
        = ∑ j ∈ Finset.range (N + 1 + 1),
          ((Nat.descFactorial (N + 1) j : ℕ) : ℂ) * n ^ j * (x + y) ^ (N + 1 - j) := by
      linear_combination hconcl
    simpa using hfinal

private lemma rho_lt_one (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_eq : ρ * Real.exp (ρ + 1) = 1) : ρ < 1 := by
  by_contra h
  have h1ρ : (1 : ℝ) ≤ ρ := not_lt.mp h
  have hexp : Real.exp 2 ≤ Real.exp (ρ + 1) := Real.exp_le_exp.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp (ρ + 1) := by
    have h23 : (2 : ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    linarith
  have hcon : (1 : ℝ) < ρ * Real.exp (ρ + 1) := by
    calc (1 : ℝ) < 1 * 3 := by norm_num
      _ ≤ ρ * Real.exp (ρ + 1) := mul_le_mul h1ρ h3 (by norm_num) hρ_pos.le
  linarith [hρ_eq]

private lemma abs_n_lt_one (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_eq : ρ * Real.exp (ρ + 1) = 1) (n : ℝ) (hn : -ρ < n ∧ n < 1) :
    |n| < 1 := by
  have hρ1 := rho_lt_one ρ hρ_pos hρ_eq
  rw [abs_lt]
  constructor <;> linarith

/-- The Jensen ratio `q = |n| * exp (1 - n)` is below one on `-ρ < n < 1`. -/
private lemma q_lt_one (ρ : ℝ)
    (hρ_eq : ρ * Real.exp (ρ + 1) = 1) (n : ℝ) (hn : -ρ < n ∧ n < 1) :
    |n| * Real.exp (1 - n) < 1 := by
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have h1 : -n < ρ := by linarith [hn.1]
    have hn_neg : (0 : ℝ) < -n := neg_pos.mpr hn0
    have he : Real.exp (-n) < Real.exp ρ := Real.exp_lt_exp.mpr h1
    have hmul := mul_lt_mul'' h1 he hn_neg.le (Real.exp_pos _).le
    have hexp1 : Real.exp (1 - n) = Real.exp 1 * Real.exp (-n) := by
      rw [← Real.exp_add]; ring_nf
    rw [abs_of_neg hn0, hexp1]
    have e11 : Real.exp 1 * Real.exp ρ = Real.exp (ρ + 1) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp 1 * ((-n) * Real.exp (-n))
        < Real.exp 1 * (ρ * Real.exp ρ) :=
      mul_lt_mul_of_pos_left hmul (Real.exp_pos _)
    have h3 : Real.exp 1 * (ρ * Real.exp ρ) = ρ * Real.exp (ρ + 1) := by
      rw [← e11]; ring
    rw [h3, hρ_eq] at h2
    linarith [h2]
  · subst hn0
    simp
  · have hn1 : n ≠ 1 := ne_of_lt hn.2
    have hlog := Real.log_lt_sub_one_of_pos hn0 hn1
    have hexp : Real.exp (1 - n) < Real.exp (-Real.log n) :=
      Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log hn0] at hexp
    rw [abs_of_pos hn0]
    have hfin := mul_lt_mul_of_pos_left hexp hn0
    rwa [mul_inv_cancel₀ (ne_of_gt hn0)] at hfin

/-- Descending factorials are bounded by powers. -/
private lemma descFactorial_le_pow (N j : ℕ) :
    Nat.descFactorial N j ≤ N ^ j := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [Nat.descFactorial_succ, pow_succ']
    exact Nat.mul_le_mul (Nat.sub_le N j) (ih N)

/-- The normalized descending factorial is at most one. -/
private lemma descFactorial_div_pow_le_one (N j : ℕ) (hN : 1 ≤ N) :
    ((Nat.descFactorial N j : ℕ) : ℝ) / (N : ℝ) ^ j ≤ 1 := by
  have hpos : (0 : ℝ) < (N : ℝ) ^ j := by
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  rw [div_le_one hpos]
  exact_mod_cast descFactorial_le_pow N j

/-- A binomial probability mass is at most one. -/
private lemma binom_prob_le_one (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    ((N.choose k : ℕ) : ℝ) * ((k : ℝ) / (N : ℝ)) ^ k *
      ((((N - k : ℕ)) : ℝ) / (N : ℝ)) ^ (N - k) ≤ 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set p : ℝ := (k : ℝ) / (N : ℝ) with hp
  set q : ℝ := (((N - k : ℕ)) : ℝ) / (N : ℝ) with hq
  have hpq : p + q = 1 := by
    rw [hp, hq, ← add_div, ← Nat.cast_add, Nat.add_sub_cancel' hk]
    exact div_self hNne
  have hsum : ∑ j ∈ Finset.range (N + 1),
      p ^ j * q ^ (N - j) * ((N.choose j : ℕ) : ℝ) = 1 := by
    have h := add_pow p q N
    rw [hpq, one_pow] at h
    exact h.symm
  have hnn : ∀ j ∈ Finset.range (N + 1),
      0 ≤ p ^ j * q ^ (N - j) * ((N.choose j : ℕ) : ℝ) := by
    intro j _
    apply mul_nonneg _ (Nat.cast_nonneg _)
    apply mul_nonneg <;> apply pow_nonneg
    · exact div_nonneg (Nat.cast_nonneg _) hNpos.le
    · exact div_nonneg (Nat.cast_nonneg _) hNpos.le
  have hmem : k ∈ Finset.range (N + 1) := by
    simp only [Finset.mem_range]
    omega
  have hle := Finset.single_le_sum hnn hmem
  rw [hsum] at hle
  have hring : ((N.choose k : ℕ) : ℝ) * p ^ k * q ^ (N - k)
      = p ^ k * q ^ (N - k) * ((N.choose k : ℕ) : ℝ) := by ring
  rwa [hring]

/-- The classical `(1 + u/M)^M ≤ exp u` bound. -/
private lemma one_add_div_pow_le_exp (u : ℝ) (hu : 0 ≤ u) (M : ℕ) (hM : 1 ≤ M) :
    (1 + u / (M : ℝ)) ^ M ≤ Real.exp u := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hbase : (0 : ℝ) ≤ 1 + u / (M : ℝ) := by positivity
  have h1 : 1 + u / (M : ℝ) ≤ Real.exp (u / (M : ℝ)) := by
    have h := Real.add_one_le_exp (u / (M : ℝ))
    linarith
  have h2 := pow_le_pow_left₀ hbase h1 M
  rw [← Real.exp_nat_mul] at h2
  have h3 : (M : ℝ) * (u / (M : ℝ)) = u := by field_simp
  rwa [h3] at h2

/-- Normalized descending factorials tend to one. -/
private lemma tendsto_descFactorial_div_pow (j : ℕ) :
    Filter.Tendsto (fun N : ℕ => ((Nat.descFactorial N j : ℕ) : ℝ) / (N : ℝ) ^ j)
      Filter.atTop (nhds 1) := by
  induction j with
  | zero =>
    have heq : (fun N : ℕ => ((Nat.descFactorial N 0 : ℕ) : ℝ) / (N : ℝ) ^ 0)
        = (fun _ : ℕ => (1 : ℝ)) := by
      funext N
      simp
    rw [heq]
    exact tendsto_const_nhds
  | succ j ih =>
    have hpt : ∀ N : ℕ, ((Nat.descFactorial N (j + 1) : ℕ) : ℝ) / (N : ℝ) ^ (j + 1)
        = (((Nat.descFactorial N j : ℕ) : ℝ) / (N : ℝ) ^ j) *
          ((((N - j : ℕ)) : ℝ) / (N : ℝ)) := by
      intro N
      rw [Nat.descFactorial_succ, pow_succ]
      push_cast
      rw [div_mul_div_comm]
      ring
    have hlim2 : Filter.Tendsto (fun N : ℕ => ((((N - j : ℕ)) : ℝ) / (N : ℝ)))
        Filter.atTop (nhds 1) := by
      have hev : (fun N : ℕ => ((((N - j : ℕ)) : ℝ) / (N : ℝ)))
          =ᶠ[Filter.atTop] (fun N : ℕ => 1 - (j : ℝ) / (N : ℝ)) := by
        have h0 := Filter.eventually_ge_atTop (max j 1)
        apply h0.mono
        intro N hN
        have hjN : j ≤ N := le_trans (Nat.le_max_left _ _) hN
        have hN1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hN
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        change ((((N - j : ℕ)) : ℝ) / (N : ℝ)) = 1 - (j : ℝ) / (N : ℝ)
        rw [Nat.cast_sub hjN, sub_div, div_self hNne]
      have hzero : Filter.Tendsto (fun N : ℕ => (j : ℝ) / (N : ℝ))
          Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have h1 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) - (j : ℝ) / (N : ℝ))
          Filter.atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub hzero
      rw [sub_zero] at h1
      exact h1.congr' hev.symm
    have hmul := ih.mul hlim2
    rw [mul_one] at hmul
    exact hmul.congr' (Filter.Eventually.of_forall fun N => (hpt N).symm)

/-- The exponential limit `(1 - w/N)^N → exp (-w)`. -/
private lemma tendsto_one_sub_div_pow_exp (w : ℂ) :
    Filter.Tendsto (fun N : ℕ => (1 - w / (N : ℂ)) ^ N) Filter.atTop
      (nhds (Complex.exp (-w))) := by
  refine Complex.tendsto_pow_exp_of_isLittleO_sub_add_div (-w) ?_
  have h0 : (fun n : ℕ => (1 - w / (n : ℂ)) - (1 + -w / (n : ℂ))) = fun _ => 0 := by
    funext n
    ring
  rw [h0]
  exact Asymptotics.isLittleO_zero _ _

/-- Shifted exponential limit `(1 - w/N)^(N-k) → exp (-w)`. -/
private lemma tendsto_one_sub_div_pow_shift (w : ℂ) (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => (1 - w / (N : ℂ)) ^ (N - k)) Filter.atTop
      (nhds (Complex.exp (-w))) := by
  have hbase := tendsto_one_sub_div_pow_exp w
  have hden : Filter.Tendsto (fun N : ℕ => (1 - w / (N : ℂ)) ^ k) Filter.atTop
      (nhds 1) := by
    have h0 : Filter.Tendsto (fun N : ℕ => w / (N : ℂ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat w
    have h1 : Filter.Tendsto (fun N : ℕ => (1 : ℂ) - w / (N : ℂ)) Filter.atTop
        (nhds (1 - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h1
    have h2 := h1.pow k
    simpa using h2
  have hdiv := hbase.div hden one_ne_zero
  rw [div_one] at hdiv
  apply hdiv.congr'
  have h0 := Filter.eventually_ge_atTop (k + 1)
  apply h0.mono
  intro N hN
  have hkN : k < N := by omega
  have hkNle : k ≤ N := le_of_lt hkN
  change (1 - w / (N : ℂ)) ^ N / (1 - w / (N : ℂ)) ^ k
    = (1 - w / (N : ℂ)) ^ (N - k)
  by_cases ha : (1 - w / (N : ℂ)) = 0
  · rw [ha]
    have hNk : N - k ≠ 0 := by omega
    have hN0 : N ≠ 0 := by omega
    rw [zero_pow hNk]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [pow_zero, div_one]
      exact zero_pow hN0
    · rw [zero_pow hN0, zero_pow hk0, div_zero]
  · have hak : (1 - w / (N : ℂ)) ^ k ≠ 0 := pow_ne_zero k ha
    have hsplit : (1 - w / (N : ℂ)) ^ N
        = (1 - w / (N : ℂ)) ^ (N - k) * (1 - w / (N : ℂ)) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkNle]
    rw [hsplit]
    exact mul_div_cancel_right₀ _ hak

/-- Normalized finite Jensen summand (left side). -/
private noncomputable def jensenF (x : ℂ) (n : ℝ) (N k : ℕ) : ℂ :=
  if k ≤ N then ((N.choose k : ℕ) : ℂ) * (x + (k : ℂ) * (n : ℂ)) ^ k *
    ((N : ℂ) - x - (k : ℂ) * (n : ℂ)) ^ (N - k) / (N : ℂ) ^ N
  else 0

/-- Normalized finite Jensen summand (right side). -/
private noncomputable def jensenG (n : ℝ) (N j : ℕ) : ℂ :=
  if j ≤ N then ((Nat.descFactorial N j : ℕ) : ℂ) * (n : ℂ) ^ j *
    ((N : ℂ) ^ (N - j)) / (N : ℂ) ^ N
  else 0

/-- Pointwise limit of `jensenF`. -/
private noncomputable def jensenL (x : ℂ) (n : ℝ) (k : ℕ) : ℂ :=
  (x + (k : ℂ) * (n : ℂ)) ^ k / ((Nat.factorial k : ℕ) : ℂ) *
    Complex.exp (-(x + (k : ℂ) * (n : ℂ)))

private lemma jensenF_of_le (x : ℂ) (n : ℝ) (N k : ℕ) (hk : k ≤ N) :
    jensenF x n N k = ((N.choose k : ℕ) : ℂ) * (x + (k : ℂ) * (n : ℂ)) ^ k *
      ((N : ℂ) - x - (k : ℂ) * (n : ℂ)) ^ (N - k) / (N : ℂ) ^ N := by
  unfold jensenF
  simp only [hk, ite_true]

private lemma jensenF_of_gt (x : ℂ) (n : ℝ) (N k : ℕ) (hk : ¬ k ≤ N) :
    jensenF x n N k = 0 := by
  unfold jensenF
  simp only [hk, ite_false]

private lemma jensenG_of_le (n : ℝ) (N j : ℕ) (hj : j ≤ N) :
    jensenG n N j = ((Nat.descFactorial N j : ℕ) : ℂ) * (n : ℂ) ^ j *
      ((N : ℂ) ^ (N - j)) / (N : ℂ) ^ N := by
  unfold jensenG
  simp only [hj, ite_true]

private lemma jensenG_of_gt (n : ℝ) (N j : ℕ) (hj : ¬ j ≤ N) :
    jensenG n N j = 0 := by
  unfold jensenG
  simp only [hj, ite_false]

/-- The finite Jensen identity, divided by `N^N`. -/
private lemma tsum_jensenF_eq_tsum_jensenG (x : ℂ) (n : ℝ) (N : ℕ) :
    ∑' k, jensenF x n N k = ∑' j, jensenG n N j := by
  have hF : ∑' k, jensenF x n N k
      = (∑ k ∈ Finset.range (N + 1), ((N.choose k : ℕ) : ℂ) *
        (x + (k : ℂ) * (n : ℂ)) ^ k *
        ((N : ℂ) - x - (k : ℂ) * (n : ℂ)) ^ (N - k)) / (N : ℂ) ^ N := by
    have hsupp : ∀ k ∉ Finset.range (N + 1), jensenF x n N k = 0 := by
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      exact jensenF_of_gt x n N k (by omega)
    rw [tsum_eq_sum hsupp]
    have hsum : ∑ k ∈ Finset.range (N + 1), jensenF x n N k
        = ∑ k ∈ Finset.range (N + 1), (((N.choose k : ℕ) : ℂ) *
          (x + (k : ℂ) * (n : ℂ)) ^ k *
          ((N : ℂ) - x - (k : ℂ) * (n : ℂ)) ^ (N - k) / (N : ℂ) ^ N) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      exact jensenF_of_le x n N k (by omega)
    rw [hsum, Finset.sum_div]
  have hG : ∑' j, jensenG n N j
      = (∑ j ∈ Finset.range (N + 1), ((Nat.descFactorial N j : ℕ) : ℂ) *
        (n : ℂ) ^ j * ((N : ℂ) ^ (N - j))) / (N : ℂ) ^ N := by
    have hsupp : ∀ j ∉ Finset.range (N + 1), jensenG n N j = 0 := by
      intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      exact jensenG_of_gt n N j (by omega)
    rw [tsum_eq_sum hsupp]
    have hsum : ∑ j ∈ Finset.range (N + 1), jensenG n N j
        = ∑ j ∈ Finset.range (N + 1), (((Nat.descFactorial N j : ℕ) : ℂ) *
          (n : ℂ) ^ j * ((N : ℂ) ^ (N - j)) / (N : ℂ) ^ N) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      exact jensenG_of_le n N j (by omega)
    rw [hsum, Finset.sum_div]
  rw [hF, hG]
  have hfin := finite_jensen_sum N x ((N : ℂ) - x) (n : ℂ)
  have hxy : x + ((N : ℂ) - x) = (N : ℂ) := by ring
  rw [hxy] at hfin
  rw [hfin]

/-- Pointwise limit of the right-hand side. -/
private lemma tendsto_jensenG (n : ℝ) (j : ℕ) :
    Filter.Tendsto (fun N => jensenG n N j) Filter.atTop (nhds ((n : ℂ) ^ j)) := by
  have hreal := tendsto_descFactorial_div_pow j
  have hofReal : Filter.Tendsto
      (fun N : ℕ => (((((Nat.descFactorial N j : ℕ) : ℝ) / (N : ℝ) ^ j : ℝ)) : ℂ))
      Filter.atTop (nhds 1) := by
    have hcomp := (Complex.continuous_ofReal.tendsto 1).comp hreal
    rw [Complex.ofReal_one] at hcomp
    exact hcomp
  have hconst : Filter.Tendsto (fun _ : ℕ => (n : ℂ) ^ j) Filter.atTop
      (nhds ((n : ℂ) ^ j)) := tendsto_const_nhds
  have hmul := hofReal.mul hconst
  rw [one_mul] at hmul
  apply hmul.congr'
  have hid : ∀ N : ℕ, j ≤ N → 1 ≤ N →
      (((((Nat.descFactorial N j : ℕ) : ℝ) / (N : ℝ) ^ j : ℝ)) : ℂ) * (n : ℂ) ^ j
        = jensenG n N j := by
    intro N hjN hN1
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hNpow : (N : ℂ) ^ N = (N : ℂ) ^ j * (N : ℂ) ^ (N - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hjN]
    have hMm : (N : ℂ) ^ (N - j) ≠ 0 := pow_ne_zero _ hNne
    have hcast : (((((Nat.descFactorial N j : ℕ) : ℝ) / (N : ℝ) ^ j : ℝ)) : ℂ)
        = ((Nat.descFactorial N j : ℕ) : ℂ) / (N : ℂ) ^ j := by
      push_cast
      ring
    rw [hcast, jensenG_of_le n N j hjN, hNpow, ← div_mul_div_comm,
      div_self hMm, mul_one, div_mul_eq_mul_div]
  have h0 := Filter.eventually_ge_atTop (max j 1)
  apply h0.mono
  intro N hN
  exact hid N (le_trans (Nat.le_max_left _ _) hN) (le_trans (Nat.le_max_right _ _) hN)

/-- Domination for the right-hand side. -/
private lemma norm_jensenG_le (n : ℝ) (N j : ℕ) (hN : 1 ≤ N) :
    ‖jensenG n N j‖ ≤ |n| ^ j := by
  by_cases hj : j ≤ N
  · rw [jensenG_of_le n N j hj]
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hpow : (N : ℝ) ^ N = (N : ℝ) ^ j * (N : ℝ) ^ (N - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    have hMme : (N : ℝ) ^ (N - j) ≠ 0 := pow_ne_zero _ (ne_of_gt hNpos)
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs]
    rw [hpow, ← div_mul_div_comm, div_self hMme, mul_one, ← div_mul_eq_mul_div]
    have hle := descFactorial_div_pow_le_one N j hN
    calc ((Nat.descFactorial N j : ℕ) : ℝ) / (N : ℝ) ^ j * |n| ^ j
        ≤ 1 * |n| ^ j :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg (abs_nonneg _) _)
      _ = |n| ^ j := one_mul _
  · rw [jensenG_of_gt n N j hj, norm_zero]
    exact pow_nonneg (abs_nonneg _) _

/-- The right-hand side tends to the geometric sum. -/
private lemma tendsto_tsum_jensenG (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_eq : ρ * Real.exp (ρ + 1) = 1) (n : ℝ) (hn : -ρ < n ∧ n < 1) :
    Filter.Tendsto (fun N => ∑' j, jensenG n N j) Filter.atTop
      (nhds (1 / (1 - (n : ℂ)))) := by
  have habs : |n| < 1 := abs_n_lt_one ρ hρ_pos hρ_eq n hn
  have hM : Summable (fun j : ℕ => |n| ^ j) := by
    apply summable_geometric_of_norm_lt_one
    rwa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  have hdom : ∀ᶠ N : ℕ in Filter.atTop, ∀ j, ‖jensenG n N j‖ ≤ |n| ^ j := by
    have h0 := Filter.eventually_ge_atTop 1
    apply h0.mono
    intro N hN j
    exact norm_jensenG_le n N j hN
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun N j => jensenG n N j) (g := fun j => (n : ℂ) ^ j)
    (bound := fun j => |n| ^ j) hM (fun j => tendsto_jensenG n j) hdom
  have hnorm : ‖(n : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact habs
  have hgeom : ∑' j : ℕ, (n : ℂ) ^ j = 1 / (1 - (n : ℂ)) := by
    rw [one_div]
    exact tsum_geometric_of_norm_lt_one hnorm
  rw [hgeom] at hlim
  exact hlim

/-- Pointwise limit of the left-hand side. -/
private lemma tendsto_jensenF (x : ℂ) (n : ℝ) (k : ℕ) :
    Filter.Tendsto (fun N => jensenF x n N k) Filter.atTop (nhds (jensenL x n k)) := by
  have hreal := tendsto_descFactorial_div_pow k
  have hofReal : Filter.Tendsto
      (fun N : ℕ => (((((Nat.descFactorial N k : ℕ) : ℝ) / (N : ℝ) ^ k : ℝ)) : ℂ))
      Filter.atTop (nhds 1) := by
    have hcomp := (Complex.continuous_ofReal.tendsto 1).comp hreal
    rw [Complex.ofReal_one] at hcomp
    exact hcomp
  have hexp := tendsto_one_sub_div_pow_shift (x + (k : ℂ) * (n : ℂ)) k
  have hconst : Filter.Tendsto
      (fun _ : ℕ => (x + (k : ℂ) * (n : ℂ)) ^ k / ((Nat.factorial k : ℕ) : ℂ))
      Filter.atTop
      (nhds ((x + (k : ℂ) * (n : ℂ)) ^ k / ((Nat.factorial k : ℕ) : ℂ))) :=
    tendsto_const_nhds
  have hmul := (hconst.mul hofReal).mul hexp
  rw [mul_one] at hmul
  apply hmul.congr'
  have hid : ∀ N : ℕ, k ≤ N → 1 ≤ N →
      ((x + (k : ℂ) * (n : ℂ)) ^ k / ((Nat.factorial k : ℕ) : ℂ)) *
        (((((Nat.descFactorial N k : ℕ) : ℝ) / (N : ℝ) ^ k : ℝ)) : ℂ) *
        ((1 - (x + (k : ℂ) * (n : ℂ)) / (N : ℂ)) ^ (N - k))
        = jensenF x n N k := by
    intro N hkN hN1
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hNpow : (N : ℂ) ^ N = (N : ℂ) ^ k * (N : ℂ) ^ (N - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hkN]
    have hFne : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hNkne : (N : ℂ) ^ k ≠ 0 := pow_ne_zero _ hNne
    have hMme : (N : ℂ) ^ (N - k) ≠ 0 := pow_ne_zero _ hNne
    have hC : ((N.choose k : ℕ) : ℂ)
        = ((Nat.descFactorial N k : ℕ) : ℂ) / ((Nat.factorial k : ℕ) : ℂ) := by
      have hnat := Nat.descFactorial_eq_factorial_mul_choose N k
      have hcast : ((((Nat.factorial k * N.choose k : ℕ))) : ℂ)
          = ((Nat.descFactorial N k : ℕ) : ℂ) := by exact_mod_cast hnat.symm
      rw [eq_div_iff hFne]
      calc ((N.choose k : ℕ) : ℂ) * ((Nat.factorial k : ℕ) : ℂ)
          = ((((Nat.factorial k * N.choose k : ℕ))) : ℂ) := by push_cast; ring
        _ = ((Nat.descFactorial N k : ℕ) : ℂ) := hcast
    have hcast : (((((Nat.descFactorial N k : ℕ) : ℝ) / (N : ℝ) ^ k : ℝ)) : ℂ)
        = ((Nat.descFactorial N k : ℕ) : ℂ) / (N : ℂ) ^ k := by
      push_cast
      ring
    have hbase : (N : ℂ) - x - (k : ℂ) * (n : ℂ)
        = (N : ℂ) - (x + (k : ℂ) * (n : ℂ)) := by ring
    have h1w : (1 : ℂ) - (x + (k : ℂ) * (n : ℂ)) / (N : ℂ)
        = ((N : ℂ) - (x + (k : ℂ) * (n : ℂ))) / (N : ℂ) := by
      rw [sub_div, div_self hNne]
    have heN : ((1 : ℂ) - (x + (k : ℂ) * (n : ℂ)) / (N : ℂ)) ^ (N - k)
        = ((N : ℂ) - (x + (k : ℂ) * (n : ℂ))) ^ (N - k) / (N : ℂ) ^ (N - k) := by
      rw [h1w, div_pow]
    rw [jensenF_of_le x n N k hkN, hC, hNpow, hcast, hbase, heN]
    field_simp
  have h0 := Filter.eventually_ge_atTop (max k 1)
  apply h0.mono
  intro N hN
  exact hid N (le_trans (Nat.le_max_left _ _) hN) (le_trans (Nat.le_max_right _ _) hN)

/-- First-factor bound for the left side. -/
private lemma jensenF_R1_le (x : ℂ) (n : ℝ) (k : ℕ) (hk0 : 0 < k) :
    (‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ)) ^ k ≤ (|n| + ‖x‖ / (k : ℝ)) ^ k := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hle : ‖x + (k : ℂ) * (n : ℂ)‖ ≤ ‖x‖ + (k : ℝ) * |n| := by
    have h := norm_add_le x ((k : ℂ) * (n : ℂ))
    rwa [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at h
  have hnn : (0 : ℝ) ≤ ‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ) :=
    div_nonneg (norm_nonneg _) hkpos.le
  have hle2 : ‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ) ≤ |n| + ‖x‖ / (k : ℝ) := by
    rw [div_le_iff₀ hkpos, add_mul, div_mul_cancel₀ _ hkne]
    linarith [hle]
  exact pow_le_pow_left₀ hnn hle2 k

/-- Second-factor bound for the left side. -/
private lemma jensenF_R2_le (x : ℂ) (n : ℝ) (N k : ℕ) (hkN : k < N) (hn1 : n < 1) :
    (‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)) ^ (N - k)
      ≤ Real.exp ((k : ℝ) * (1 - n) + ‖x‖) := by
  have hkNle : k ≤ N := le_of_lt hkN
  have hM1 : 1 ≤ N - k := by omega
  have hMNpos : (0 : ℝ) < (((N - k : ℕ)) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hkN
  have hMNne : ((((N - k : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hMNpos
  have hdecomp : (N : ℂ) - x - (k : ℂ) * (n : ℂ)
      = ((N - k : ℕ) : ℂ) + Complex.ofReal ((k : ℝ) * (1 - n)) - x := by
    have h1 : ((N - k : ℕ) : ℂ) = (N : ℂ) - (k : ℂ) := by
      rw [Nat.cast_sub hkNle]
    rw [h1]
    push_cast
    ring
  have hQle : ‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖
      ≤ (((N - k : ℕ)) : ℝ) + (k : ℝ) * |1 - n| + ‖x‖ := by
    have h1 : ‖((N - k : ℕ) : ℂ) + Complex.ofReal ((k : ℝ) * (1 - n))‖
        ≤ (((N - k : ℕ)) : ℝ) + (k : ℝ) * |1 - n| := by
      have h := norm_add_le ((N - k : ℕ) : ℂ) (Complex.ofReal ((k : ℝ) * (1 - n)))
      rw [Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _)] at h
      exact h
    rw [hdecomp, sub_eq_add_neg]
    calc ‖((N - k : ℕ) : ℂ) + Complex.ofReal ((k : ℝ) * (1 - n)) + (-x)‖
        ≤ ‖((N - k : ℕ) : ℂ) + Complex.ofReal ((k : ℝ) * (1 - n))‖ + ‖-x‖ :=
          norm_add_le _ _
      _ = ‖((N - k : ℕ) : ℂ) + Complex.ofReal ((k : ℝ) * (1 - n))‖ + ‖x‖ := by
          rw [norm_neg]
      _ ≤ ((((N - k : ℕ)) : ℝ) + (k : ℝ) * |1 - n|) + ‖x‖ := by
          linarith [h1]
  have hbase : ‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)
      ≤ 1 + ((k : ℝ) * |1 - n| + ‖x‖) / (((N - k : ℕ)) : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hQle hMNpos.le
    have heq : ((((N - k : ℕ)) : ℝ) + (k : ℝ) * |1 - n| + ‖x‖)
        / (((N - k : ℕ)) : ℝ)
        = 1 + ((k : ℝ) * |1 - n| + ‖x‖) / (((N - k : ℕ)) : ℝ) := by
      have hM : ((((N - k : ℕ)) : ℝ) + (k : ℝ) * |1 - n| + ‖x‖)
          = (((N - k : ℕ)) : ℝ) + ((k : ℝ) * |1 - n| + ‖x‖) := by ring
      rw [hM, add_div, div_self hMNne]
    rwa [heq] at hdiv
  have hu : (0 : ℝ) ≤ (k : ℝ) * |1 - n| + ‖x‖ := by positivity
  have hpow : (‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)) ^ (N - k)
      ≤ (1 + ((k : ℝ) * |1 - n| + ‖x‖) / (((N - k : ℕ)) : ℝ)) ^ (N - k) :=
    pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hMNpos.le) hbase _
  have hexp : (1 + ((k : ℝ) * |1 - n| + ‖x‖) / (((N - k : ℕ)) : ℝ)) ^ (N - k)
      ≤ Real.exp ((k : ℝ) * |1 - n| + ‖x‖) :=
    one_add_div_pow_le_exp ((k : ℝ) * |1 - n| + ‖x‖) hu (N - k) hM1
  have habs1 : |1 - n| = 1 - n := abs_of_pos (by linarith)
  rw [habs1] at hpow hexp
  exact le_trans hpow hexp

/-- Power-factor bound for the left side. -/
private lemma jensenF_pow_le (x : ℂ) (n : ℝ) (k : ℕ) (hk0 : 0 < k) (hn0 : n ≠ 0) :
    (|n| + ‖x‖ / (k : ℝ)) ^ k ≤ |n| ^ k * Real.exp (‖x‖ / |n|) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have habs : (0 : ℝ) < |n| := abs_pos.mpr hn0
  have habs_ne : |n| ≠ 0 := ne_of_gt habs
  have hfac : |n| + ‖x‖ / (k : ℝ) = |n| * (1 + (‖x‖ / |n|) / (k : ℝ)) := by
    have h1 : |n| * ((‖x‖ / |n|) / (k : ℝ)) = ‖x‖ / (k : ℝ) := by
      rw [div_div, ← mul_div_assoc, mul_div_mul_left _ _ habs_ne]
    rw [mul_add, mul_one, h1]
  rw [hfac, mul_pow]
  have hnn : (0 : ℝ) ≤ |n| ^ k := pow_nonneg habs.le _
  have hle : (1 + (‖x‖ / |n|) / (k : ℝ)) ^ k ≤ Real.exp (‖x‖ / |n|) :=
    one_add_div_pow_le_exp (‖x‖ / |n|) (div_nonneg (norm_nonneg _) habs.le) k hk0
  exact mul_le_mul_of_nonneg_left hle hnn

/-- Domination for the left side, middle case. -/
private lemma norm_jensenF_mid (x : ℂ) (n : ℝ) (N k : ℕ) (hN : 1 ≤ N)
    (hk0 : 0 < k) (hkN : k < N) (hn1 : n < 1) (hn0 : n ≠ 0) :
    ‖jensenF x n N k‖
      ≤ Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) * (|n| * Real.exp (1 - n)) ^ k := by
  have hkNle : k ≤ N := le_of_lt hkN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hMNpos : (0 : ℝ) < (((N - k : ℕ)) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hkN
  have hMNne : ((((N - k : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hMNpos
  have habs : (0 : ℝ) < |n| := abs_pos.mpr hn0
  have hnorm : ‖jensenF x n N k‖
      = ((N.choose k : ℕ) : ℝ) * ‖x + (k : ℂ) * (n : ℂ)‖ ^ k *
        ‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ ^ (N - k) / (N : ℝ) ^ N := by
    rw [jensenF_of_le x n N k hkNle]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  rw [hnorm]
  have hpow : (N : ℝ) ^ N = (N : ℝ) ^ k * (N : ℝ) ^ (N - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkNle]
  have hB := binom_prob_le_one N k hN hkNle
  have hkk : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ hkne
  have hMM : ((((N - k : ℕ)) : ℝ)) ^ (N - k) ≠ 0 := pow_ne_zero _ hMNne
  have hNk : (N : ℝ) ^ k ≠ 0 := pow_ne_zero _ hNne
  have hNM : (N : ℝ) ^ (N - k) ≠ 0 := pow_ne_zero _ hNne
  have hfactor : ((N.choose k : ℕ) : ℝ) * ‖x + (k : ℂ) * (n : ℂ)‖ ^ k *
        ‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ ^ (N - k) / (N : ℝ) ^ N
      = (((N.choose k : ℕ) : ℝ) * ((k : ℝ) / (N : ℝ)) ^ k *
        ((((N - k : ℕ)) : ℝ) / (N : ℝ)) ^ (N - k))
        * ((‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ)) ^ k *
          (‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)) ^ (N - k)) := by
    rw [hpow]
    simp only [div_pow]
    field_simp
  rw [hfactor]
  have hRnn : (0 : ℝ) ≤ (‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ)) ^ k *
      (‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)) ^ (N - k) := by
    positivity
  have hBle1 : (((N.choose k : ℕ) : ℝ) * ((k : ℝ) / (N : ℝ)) ^ k *
        ((((N - k : ℕ)) : ℝ) / (N : ℝ)) ^ (N - k))
        * ((‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ)) ^ k *
          (‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)) ^ (N - k))
      ≤ (‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ)) ^ k *
        (‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)) ^ (N - k) := by
    have h := mul_le_mul_of_nonneg_right hB hRnn
    rwa [one_mul] at h
  apply le_trans hBle1
  have hR1 := jensenF_R1_le x n k hk0
  have hR2 := jensenF_R2_le x n N k hkN hn1
  have hR1b := jensenF_pow_le x n k hk0 hn0
  calc (‖x + (k : ℂ) * (n : ℂ)‖ / (k : ℝ)) ^ k *
        (‖(N : ℂ) - x - (k : ℂ) * (n : ℂ)‖ / (((N - k : ℕ)) : ℝ)) ^ (N - k)
      ≤ (|n| + ‖x‖ / (k : ℝ)) ^ k * Real.exp ((k : ℝ) * (1 - n) + ‖x‖) :=
        mul_le_mul hR1 hR2 (by positivity) (by positivity)
    _ ≤ (|n| ^ k * Real.exp (‖x‖ / |n|)) *
        (Real.exp ((k : ℝ) * (1 - n)) * Real.exp ‖x‖) := by
        rw [Real.exp_add]
        exact mul_le_mul hR1b le_rfl (by positivity) (by positivity)
    _ = Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) * (|n| * Real.exp (1 - n)) ^ k := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring

/-- Domination for the left side, top case. -/
private lemma norm_jensenF_top (x : ℂ) (n : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hn1 : n < 1) (hn0 : n ≠ 0) :
    ‖jensenF x n N N‖
      ≤ Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) * (|n| * Real.exp (1 - n)) ^ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hnorm : ‖jensenF x n N N‖
      = ‖x + (N : ℂ) * (n : ℂ)‖ ^ N / (N : ℝ) ^ N := by
    rw [jensenF_of_le x n N N le_rfl]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    rw [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one]
  rw [hnorm, ← div_pow]
  have hR1 := jensenF_R1_le x n N (by omega : 0 < N)
  apply le_trans hR1
  have hP := jensenF_pow_le x n N (by omega : 0 < N) hn0
  apply le_trans hP
  have hqpow : (|n| * Real.exp (1 - n)) ^ N
      = |n| ^ N * Real.exp ((N : ℝ) * (1 - n)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  rw [hqpow]
  have h1 : (1 : ℝ) ≤ Real.exp ‖x‖ * Real.exp ((N : ℝ) * (1 - n)) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    have h1n : (0 : ℝ) ≤ 1 - n := by linarith
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith [norm_nonneg x, mul_nonneg hNnn h1n]
  have hnn : (0 : ℝ) ≤ |n| ^ N * Real.exp (‖x‖ / |n|) := by positivity
  have heq : Real.exp ‖x‖ * Real.exp (‖x‖ / |n|)
      * (|n| ^ N * Real.exp ((N : ℝ) * (1 - n)))
      = (|n| ^ N * Real.exp (‖x‖ / |n|))
        * (Real.exp ‖x‖ * Real.exp ((N : ℝ) * (1 - n))) := by ring
  rw [heq]
  exact le_mul_of_one_le_right hnn h1

/-- Domination for the left side, bottom case. -/
private lemma norm_jensenF_zero (x : ℂ) (n : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖jensenF x n N 0‖
      ≤ Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) * (|n| * Real.exp (1 - n)) ^ 0 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hnorm : ‖jensenF x n N 0‖ = ‖(N : ℂ) - x‖ ^ N / (N : ℝ) ^ N := by
    rw [jensenF_of_le x n N 0 (Nat.zero_le _)]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, pow_zero, Nat.sub_zero,
      zero_mul, sub_zero, one_mul, mul_one]
  rw [hnorm, ← div_pow, pow_zero, mul_one]
  have hbase : ‖(N : ℂ) - x‖ / (N : ℝ) ≤ 1 + ‖x‖ / (N : ℝ) := by
    have hle : ‖(N : ℂ) - x‖ ≤ (N : ℝ) + ‖x‖ := by
      have h := norm_sub_le (N : ℂ) x
      rwa [Complex.norm_natCast] at h
    have hdiv := div_le_div_of_nonneg_right hle hNpos.le
    have heq : ((N : ℝ) + ‖x‖) / (N : ℝ) = 1 + ‖x‖ / (N : ℝ) := by
      rw [add_div, div_self (ne_of_gt hNpos)]
    rwa [heq] at hdiv
  have hpow : (‖(N : ℂ) - x‖ / (N : ℝ)) ^ N ≤ (1 + ‖x‖ / (N : ℝ)) ^ N :=
    pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hNpos.le) hbase _
  have hexp : (1 + ‖x‖ / (N : ℝ)) ^ N ≤ Real.exp ‖x‖ :=
    one_add_div_pow_le_exp ‖x‖ (norm_nonneg _) N hN
  have hC : Real.exp ‖x‖ ≤ Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) :=
    le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp (div_nonneg (norm_nonneg _) (abs_nonneg _)))
  exact le_trans hpow (le_trans hexp hC)

/-- Domination for the left side. -/
private lemma norm_jensenF_le (x : ℂ) (n : ℝ) (N k : ℕ) (hN : 1 ≤ N)
    (hn1 : n < 1) (hn0 : n ≠ 0) :
    ‖jensenF x n N k‖
      ≤ Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) * (|n| * Real.exp (1 - n)) ^ k := by
  rcases lt_trichotomy k N with hk | hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact norm_jensenF_zero x n N hN
    · exact norm_jensenF_mid x n N k hN hk0 hk hn1 hn0
  · rw [hk]
    exact norm_jensenF_top x n N hN hn1 hn0
  · rw [jensenF_of_gt x n N k (by omega)]
    rw [norm_zero]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (pow_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) _)

/-- The left-hand side tends to the Jensen-series limit. -/
private lemma tendsto_tsum_jensenF (ρ : ℝ)
    (hρ_eq : ρ * Real.exp (ρ + 1) = 1) (n : ℝ) (hn : -ρ < n ∧ n < 1)
    (x : ℂ) (hn0 : n ≠ 0) :
    Filter.Tendsto (fun N => ∑' k, jensenF x n N k) Filter.atTop
      (nhds (∑' k, jensenL x n k)) := by
  have hq1 := q_lt_one ρ hρ_eq n hn
  have hqnn : (0 : ℝ) ≤ |n| * Real.exp (1 - n) :=
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hgeom : Summable (fun k : ℕ => (|n| * Real.exp (1 - n)) ^ k) := by
    apply summable_geometric_of_norm_lt_one
    rwa [Real.norm_eq_abs, abs_of_nonneg hqnn]
  have hM : Summable (fun k : ℕ => Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) *
      (|n| * Real.exp (1 - n)) ^ k) :=
    hgeom.mul_left _
  have hdom : ∀ᶠ N : ℕ in Filter.atTop, ∀ k,
      ‖jensenF x n N k‖ ≤ Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) *
        (|n| * Real.exp (1 - n)) ^ k := by
    have h0 := Filter.eventually_ge_atTop 1
    apply h0.mono
    intro N hN k
    exact norm_jensenF_le x n N k hN hn.2 hn0
  exact tendsto_tsum_of_dominated_convergence
    (f := fun N k => jensenF x n N k) (g := fun k => jensenL x n k)
    (bound := fun k => Real.exp ‖x‖ * Real.exp (‖x‖ / |n|) *
      (|n| * Real.exp (1 - n)) ^ k) hM (fun k => tendsto_jensenF x n k) hdom

/-- The limit series equals `exp (-x)` times the Jensen series. -/
private lemma tsum_jensenL_eq (ρ : ℝ) (hρ_pos : 0 < ρ)
    (hρ_eq : ρ * Real.exp (ρ + 1) = 1) (n : ℝ) (hn : -ρ < n ∧ n < 1) (x : ℂ) :
    ∑' k, jensenL x n k = Complex.exp (-x) * ∑' (k : ℕ),
      ((x + (k : ℂ) * (n : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))) := by
  have hS := summable_jensen_series ρ hρ_pos hρ_eq n hn x
  have hpt : ∀ k : ℕ, jensenL x n k = Complex.exp (-x) *
      ((x + (k : ℂ) * (n : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))) := by
    intro k
    have hfact : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hexp0 := Complex.exp_ne_zero ((k : ℂ) * (n : ℂ))
    have hexp : Complex.exp (-(x + (k : ℂ) * (n : ℂ)))
        = Complex.exp (-x) / Complex.exp ((k : ℂ) * (n : ℂ)) := by
      rw [eq_div_iff hexp0, ← Complex.exp_add]
      congr 1
      ring
    unfold jensenL
    rw [hexp]
    field_simp
  have hHas := hS.hasSum.mul_left (Complex.exp (-x))
  have hHasL : HasSum (fun k : ℕ => jensenL x n k) (Complex.exp (-x) * ∑' (k : ℕ),
      ((x + (k : ℂ) * (n : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ))))) := by
    have hfun : (fun k : ℕ => jensenL x n k) = (fun k : ℕ => Complex.exp (-x) *
        ((x + (k : ℂ) * (n : ℂ)) ^ k /
          ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ))))) :=
      funext hpt
    rw [hfun]
    exact hHas
  have hLsum := hHasL.summable
  have huniq := hHasL.unique hLsum.hasSum
  exact huniq.symm

/-- **Jensen's series (Chapter 3, Entry 16, Corollary 1).** Let $\rho$ be a positive real number
with $\rho e^{\rho + 1} = 1$, let $n$ be a real number with $-\rho < n < 1$, and let $x$ be a
complex number. Then the series
$$\sum_{k=0}^{\infty} \frac{(x + kn)^k}{k!\, e^{kn}}$$
converges unconditionally to $e^x / (1 - n)$.

Proves `Wanted` entry `ramanujan_part1_ch3_entry16_corollary1_jensen_series`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Corollary 1, formula (16.6),
    printed pp. 80--81 / PDF pp. 90--91.
-/
theorem ramanujan_part1_ch3_entry16_corollary1_jensen_series (ρ : ℝ)
    (hρ_pos : 0 < ρ) (hρ_eq : ρ * Real.exp (ρ + 1) = 1) (n : ℝ) (hn : -ρ < n ∧ n < 1) (x : ℂ) :
    HasSum (fun k : ℕ => (x + (k : ℂ) * (n : ℂ)) ^ k /
        ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ))))
      (Complex.exp x / (1 - (n : ℂ))) := by
  by_cases hn0 : n = 0
  · subst hn0
    exact jensen_series_zero x
  · have hS := summable_jensen_series ρ hρ_pos hρ_eq n hn x
    rw [hS.hasSum_iff]
    have hF := tendsto_tsum_jensenF ρ hρ_eq n hn x hn0
    have hG := tendsto_tsum_jensenG ρ hρ_pos hρ_eq n hn
    have hev : (fun N => ∑' k, jensenF x n N k)
        =ᶠ[Filter.atTop] (fun N => ∑' j, jensenG n N j) :=
      Filter.Eventually.of_forall (fun N => tsum_jensenF_eq_tsum_jensenG x n N)
    have hFL := tsum_jensenL_eq ρ hρ_pos hρ_eq n hn x
    have hG2 := hF.congr' hev
    have heq := tendsto_nhds_unique hG2 hG
    have hexp1 : Complex.exp x * Complex.exp (-x) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hfin : Complex.exp (-x) * (∑' (k : ℕ),
        ((x + (k : ℂ) * (n : ℂ)) ^ k /
          ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))))
        = 1 / (1 - (n : ℂ)) :=
      hFL.symm.trans heq
    calc (∑' (k : ℕ), ((x + (k : ℂ) * (n : ℂ)) ^ k /
          ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))))
        = Complex.exp x * (Complex.exp (-x) * (∑' (k : ℕ),
          ((x + (k : ℂ) * (n : ℂ)) ^ k /
            ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ)))))) := by
          rw [← mul_assoc, hexp1, one_mul]
      _ = Complex.exp x * (1 / (1 - (n : ℂ))) := by rw [hfin]
      _ = Complex.exp x / (1 - (n : ℂ)) := by rw [mul_one_div]

end Entry16Corollary1JensenSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
