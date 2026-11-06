/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9, Entry 8

Odd-harmonic power series at x/(2-x) equals (log(1-x))²/8 + Li₂(x)/2.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry8Arcsin

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry8DilogTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)

def chapter9Entry8Dilog (x : ℝ) : ℝ :=
  ∑' n : ℕ, chapter9Entry8DilogTerm x n

def chapter9OddHarmonic (n : ℕ) : ℝ :=
  ∑ j ∈ range n, 1 / ((2 * j + 1 : ℕ) : ℝ)

def chapter9Entry8FTerm (x : ℝ) (n : ℕ) : ℝ :=
  chapter9OddHarmonic (n + 1) * x ^ (2 * n + 1) /
    ((2 * n + 1 : ℕ) : ℝ)

def chapter9Entry8F (x : ℝ) : ℝ :=
  ∑' n : ℕ, chapter9Entry8FTerm x n

private lemma oddHarmonic_nonneg (n : ℕ) : 0 ≤ chapter9OddHarmonic n := by
  unfold chapter9OddHarmonic
  apply Finset.sum_nonneg
  intro j _
  positivity

private lemma oddHarmonic_le (n : ℕ) : chapter9OddHarmonic n ≤ n := by
  unfold chapter9OddHarmonic
  calc ∑ j ∈ range n, 1 / ((2 * j + 1 : ℕ) : ℝ)
      ≤ ∑ j ∈ range n, 1 := by
        apply Finset.sum_le_sum
        intro j _
        rw [div_le_one (by positivity)]
        have : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * j))
        exact this
    _ = n := by simp

private lemma summable_dilogTerm {x : ℝ} (hx : |x| < 1) :
    Summable (chapter9Entry8DilogTerm x) := by
  have hax : |(|x|)| < 1 := by rwa [abs_abs]
  have hgeo : Summable (fun n : ℕ => |x| ^ (n + 1)) := by
    simpa [pow_succ] using (summable_geometric_of_abs_lt_one hax).mul_right |x|
  apply Summable.of_norm_bounded hgeo
  intro n
  show ‖chapter9Entry8DilogTerm x n‖ ≤ |x| ^ (n + 1)
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have h2 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) ^ 2 := one_le_pow₀ h1
  have hnn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have habs : |(((n + 1 : ℕ)) : ℝ)| = (((n + 1 : ℕ)) : ℝ) := abs_of_nonneg hnn
  unfold chapter9Entry8DilogTerm
  simp only [norm_div, norm_pow, Real.norm_eq_abs, habs]
  exact div_le_self (by positivity) h2

private lemma summable_FTerm {z : ℝ} (hz : |z| < 1) :
    Summable (chapter9Entry8FTerm z) := by
  have hsq : |z| ^ 2 < 1 := by nlinarith [hz, abs_nonneg z]
  have hnn2 : (0 : ℝ) ≤ |z| ^ 2 := by positivity
  have hnorm : ‖(|z| ^ 2 : ℝ)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn2]
  have habs1 : |(|z| ^ 2 : ℝ)| < 1 := by
    rwa [abs_of_nonneg hnn2]
  have hpow : ∀ n : ℕ, |z| ^ (2 * n + 1) = |z| * (|z| ^ 2) ^ n := by
    intro n
    rw [pow_succ, ← pow_mul]
    ring
  have h1' : Summable (fun n : ℕ => (n : ℝ) * ((|z| ^ 2) ^ n)) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2 : Summable (fun n : ℕ => ((|z| ^ 2) ^ n)) :=
    summable_geometric_of_abs_lt_one habs1
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) * (|z| * (|z| ^ 2) ^ n)) := by
    have e : (fun n : ℕ => ((n : ℝ) + 1) * (|z| * (|z| ^ 2) ^ n))
        = fun n : ℕ => |z| * ((n : ℝ) * ((|z| ^ 2) ^ n) + (|z| ^ 2) ^ n) := by
      funext n
      ring
    rw [e]
    exact (h1'.add h2).mul_left |z|
  apply Summable.of_norm_bounded hsum
  intro n
  have hH : |chapter9OddHarmonic (n + 1)| ≤ ((n : ℝ) + 1) := by
    rw [abs_of_nonneg (oddHarmonic_nonneg _)]
    calc chapter9OddHarmonic (n + 1) ≤ (((n + 1 : ℕ)) : ℝ) := by
          exact_mod_cast oddHarmonic_le (n + 1)
      _ = (n : ℝ) + 1 := by push_cast; ring
  have hnn3 : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have habs3 : |(((2 * n + 1 : ℕ)) : ℝ)| = (((2 * n + 1 : ℕ)) : ℝ) :=
    abs_of_nonneg hnn3
  have hD1 : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * n))
  have hMnn : (0 : ℝ) ≤ |z| * (|z| ^ 2) ^ n := by positivity
  unfold chapter9Entry8FTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, habs3]
  calc |chapter9OddHarmonic (n + 1)| * |z| ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)
      = |chapter9OddHarmonic (n + 1)| * (|z| * (|z| ^ 2) ^ n)
          / ((2 * n + 1 : ℕ) : ℝ) := by rw [hpow n]
    _ ≤ ((n : ℝ) + 1) * (|z| * (|z| ^ 2) ^ n) / ((2 * n + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hnn3
        exact mul_le_mul_of_nonneg_right hH hMnn
    _ ≤ ((n : ℝ) + 1) * (|z| * (|z| ^ 2) ^ n) := by
        apply div_le_self (by positivity)
        exact hD1

private lemma abs_sq_lt_one_of_abs_lt_one {t : ℝ} (ht : |t| < 1) : |t ^ 2| < 1 := by
  rw [abs_pow]
  nlinarith [ht, abs_nonneg t]

private lemma hasSum_even_log {t : ℝ} (ht : |t| < 1) :
    HasSum (fun j : ℕ => t ^ (2 * j + 2) / (((2 * j + 2 : ℕ)) : ℝ))
      (-Real.log (1 - t ^ 2) / 2) := by
  have hsq1 : |t ^ 2| < 1 := abs_sq_lt_one_of_abs_lt_one ht
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := t ^ 2) hsq1
  have e : (fun n : ℕ => (t ^ 2) ^ (n + 1) / ((n : ℝ) + 1))
      = fun n : ℕ => 2 * (t ^ (2 * n + 2) / (((2 * n + 2 : ℕ)) : ℝ)) := by
    funext n
    have hD : (((2 * n + 2 : ℕ)) : ℝ) = 2 * ((n : ℝ) + 1) := by
      push_cast
      ring
    have hexp : (t ^ 2) ^ (n + 1) = t ^ (2 * n + 2) := by
      rw [← pow_mul]
      congr 1
    have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    rw [hexp, hD]
    field_simp
  rw [e] at hlog
  have e2 : (fun j : ℕ => 2 * (t ^ (2 * j + 2) / (((2 * j + 2 : ℕ)) : ℝ)) / 2)
      = fun j : ℕ => t ^ (2 * j + 2) / (((2 * j + 2 : ℕ)) : ℝ) := by
    funext j
    ring
  have hE := hlog.div_const (2 : ℝ)
  rw [e2] at hE
  exact hE

private lemma summable_odd_log {t : ℝ} (ht : |t| < 1) :
    Summable (fun j : ℕ => t ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ)) := by
  have hsq1 : |t ^ 2| < 1 := abs_sq_lt_one_of_abs_lt_one ht
  have habs2 : |(|t| ^ 2 : ℝ)| < 1 := by
    have hnn : (0 : ℝ) ≤ |t| ^ 2 := by positivity
    rwa [abs_of_nonneg hnn, ← abs_pow]
  have hgeo : Summable (fun j : ℕ => (|t| ^ 2) ^ j) :=
    summable_geometric_of_abs_lt_one habs2
  have hgeo2 : Summable (fun j : ℕ => |t| * (|t| ^ 2) ^ j) := hgeo.mul_left |t|
  apply Summable.of_norm_bounded hgeo2
  intro j
  have hnn3 : (0 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have habs3 : |(((2 * j + 1 : ℕ)) : ℝ)| = (((2 * j + 1 : ℕ)) : ℝ) :=
    abs_of_nonneg hnn3
  have hD1 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * j))
  have hpow : |t| ^ (2 * j + 1) = |t| * (|t| ^ 2) ^ j := by
    rw [pow_succ, ← pow_mul]
    ring
  simp only [norm_div, norm_pow, Real.norm_eq_abs, habs3]
  rw [hpow]
  exact div_le_self (by positivity) hD1

private lemma hasSum_odd_log {t : ℝ} (ht : |t| < 1) :
    HasSum (fun j : ℕ => t ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ))
      ((Real.log (1 + t) - Real.log (1 - t)) / 2) := by
  have hW := Real.hasSum_pow_div_log_of_abs_lt_one (x := t) ht
  have hE := hasSum_even_log ht
  have hO := (summable_odd_log ht).hasSum
  have eO : (fun k : ℕ => t ^ (2 * k + 1) / ((((2 * k : ℕ)) : ℝ) + 1))
      = (fun k : ℕ => t ^ (2 * k + 1) / (((2 * k + 1 : ℕ)) : ℝ)) := by
    funext k
    congr 1
    push_cast
    ring
  have eE : (fun k : ℕ => t ^ (2 * k + 1 + 1) / ((((2 * k + 1 : ℕ)) : ℝ) + 1))
      = (fun k : ℕ => t ^ (2 * k + 2) / (((2 * k + 2 : ℕ)) : ℝ)) := by
    funext k
    have hex : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    rw [hex]
    congr 1
    push_cast
    ring
  have hEsumm : Summable (fun j : ℕ => t ^ (2 * j + 2) / (((2 * j + 2 : ℕ)) : ℝ)) :=
    hE.summable
  have hEtsum := hEsumm.hasSum
  have hWO : HasSum (fun n : ℕ => t ^ (n + 1) / ((n : ℝ) + 1))
      ((∑' j, t ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ))
        + ∑' j, t ^ (2 * j + 2) / (((2 * j + 2 : ℕ)) : ℝ)) :=
    HasSum.even_add_odd (hO.congr_fun (fun k => congrFun eO k))
      (hEtsum.congr_fun (fun k => congrFun eE k))
  have hval := HasSum.unique hW hWO
  have h1t : (0 : ℝ) < 1 - t := by
    have := abs_lt.mp ht
    linarith
  have h1t2 : (0 : ℝ) < 1 + t := by
    have := abs_lt.mp ht
    linarith
  have hlog2 : Real.log (1 - t ^ 2) = Real.log (1 - t) + Real.log (1 + t) := by
    have hfact : (1 : ℝ) - t ^ 2 = (1 - t) * (1 + t) := by ring
    rw [hfact, Real.log_mul (ne_of_gt h1t) (ne_of_gt h1t2)]
  have hE2 := hE.tsum_eq
  rw [hE2, hlog2] at hval
  have hfin : (∑' j, t ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ))
      = (Real.log (1 + t) - Real.log (1 - t)) / 2 := by
    linarith [hval]
  rw [hfin] at hO
  exact hO

private lemma summable_n1_mul_pow {s : ℝ} (hs : ‖s‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * s ^ n) := by
  have e : (fun n : ℕ => ((n : ℝ) + 1) * s ^ n)
      = fun n : ℕ => (n : ℝ) ^ 1 * s ^ n + s ^ n := by
    funext n
    simp [pow_one]
    ring
  rw [e]
  exact ((summable_pow_mul_geometric_of_norm_lt_one 1 hs).add
    (summable_geometric_of_norm_lt_one hs))

private lemma hasSum_T_eq {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => chapter9OddHarmonic (n + 1) * t ^ n)
      ((∑' j, t ^ j / (((2 * j + 1 : ℕ)) : ℝ)) / (1 - t)) := by
  have hnormt : ‖(|t| : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_abs]
  have hgeot : Summable (fun n : ℕ => |t| ^ n) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_abs])
  have ha : Summable (fun n : ℕ => chapter9OddHarmonic (n + 1) * t ^ n) := by
    have hbase := summable_n1_mul_pow (s := |t|) hnormt
    apply Summable.of_norm_bounded hbase
    intro n
    have hHn : ‖chapter9OddHarmonic (n + 1)‖ ≤ (n : ℝ) + 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (oddHarmonic_nonneg _)]
      calc chapter9OddHarmonic (n + 1) ≤ (((n + 1 : ℕ)) : ℝ) := by
            exact_mod_cast oddHarmonic_le (n + 1)
        _ = (n : ℝ) + 1 := by push_cast; ring
    calc ‖chapter9OddHarmonic (n + 1) * t ^ n‖
        = ‖chapter9OddHarmonic (n + 1)‖ * ‖t‖ ^ n := by
          rw [norm_mul, norm_pow]
      _ ≤ ((n : ℝ) + 1) * |t| ^ n := by
          have htN : ‖t‖ ^ n ≤ |t| ^ n := by rw [Real.norm_eq_abs]
          exact mul_le_mul hHn htN (by positivity) (by positivity)
  have hb : Summable (fun n : ℕ => chapter9OddHarmonic (n + 1) * t ^ (n + 1)) := by
    have e : (fun n : ℕ => chapter9OddHarmonic (n + 1) * t ^ (n + 1))
        = fun n : ℕ => t * (chapter9OddHarmonic (n + 1) * t ^ n) := by
      funext n
      ring
    rw [e]
    exact ha.mul_left t
  have hu : Summable (fun n : ℕ => t ^ n / (((2 * n + 1 : ℕ)) : ℝ)) := by
    apply Summable.of_norm_bounded hgeot
    intro n
    have hnn3 : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have habs3 : |(((2 * n + 1 : ℕ)) : ℝ)| = (((2 * n + 1 : ℕ)) : ℝ) :=
      abs_of_nonneg hnn3
    have hD1 : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * n))
    simp only [norm_div, norm_pow, Real.norm_eq_abs, habs3]
    exact div_le_self (by positivity) hD1
  have hT := ha.hasSum
  have hTt : HasSum (fun n : ℕ => chapter9OddHarmonic (n + 1) * t ^ (n + 1))
      (t * ∑' n, chapter9OddHarmonic (n + 1) * t ^ n) := by
    have h := ha.hasSum.mul_left t
    apply h.congr_fun
    intro n
    ring
  have hAB : HasSum
      (fun n : ℕ => chapter9OddHarmonic (n + 1) * t ^ n
        - chapter9OddHarmonic (n + 1) * t ^ (n + 1))
      ((∑' n, chapter9OddHarmonic (n + 1) * t ^ n)
        - t * ∑' n, chapter9OddHarmonic (n + 1) * t ^ n) :=
    hT.sub hTt
  have key : ∀ N : ℕ,
      (∑ n ∈ range N, (chapter9OddHarmonic (n + 1) * t ^ n
        - chapter9OddHarmonic (n + 1) * t ^ (n + 1)))
      = (∑ n ∈ range N, t ^ n / (((2 * n + 1 : ℕ)) : ℝ))
        - chapter9OddHarmonic N * t ^ N := by
    intro N
    induction N with
    | zero => simp [chapter9OddHarmonic]
    | succ N ih =>
      have hH : chapter9OddHarmonic (N + 1)
          = chapter9OddHarmonic N + 1 / (((2 * N + 1 : ℕ)) : ℝ) := by
        simpa [chapter9OddHarmonic] using
          Finset.sum_range_succ (fun j : ℕ => (1 : ℝ) / (((2 * j + 1 : ℕ)) : ℝ)) N
      simp only [Finset.sum_range_succ]
      rw [ih, hH]
      ring
  have herr : Summable (fun N : ℕ => (N : ℝ) * |t| ^ N) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnormt
  have herrlim : Tendsto (fun N : ℕ => chapter9OddHarmonic N * t ^ N) atTop
      (nhds 0) := by
    refine squeeze_zero_norm ?_ herr.tendsto_atTop_zero
    intro N
    have hHN : ‖chapter9OddHarmonic N‖ ≤ (N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (oddHarmonic_nonneg N)]
      exact_mod_cast oddHarmonic_le N
    calc ‖chapter9OddHarmonic N * t ^ N‖
        = ‖chapter9OddHarmonic N‖ * ‖t‖ ^ N := by rw [norm_mul, norm_pow]
      _ ≤ (N : ℝ) * |t| ^ N := by
          have htN : ‖t‖ ^ N ≤ |t| ^ N := by rw [Real.norm_eq_abs]
          exact mul_le_mul hHN htN (by positivity) (by positivity)
  have pfun : (fun N : ℕ => ∑ n ∈ range N, (chapter9OddHarmonic (n + 1) * t ^ n
      - chapter9OddHarmonic (n + 1) * t ^ (n + 1)))
      = fun N : ℕ => (∑ n ∈ range N, t ^ n / (((2 * n + 1 : ℕ)) : ℝ))
        - chapter9OddHarmonic N * t ^ N := funext key
  have hlim : Tendsto
      (fun N : ℕ => ∑ n ∈ range N, (chapter9OddHarmonic (n + 1) * t ^ n
        - chapter9OddHarmonic (n + 1) * t ^ (n + 1))) atTop
      (nhds (∑' n, t ^ n / (((2 * n + 1 : ℕ)) : ℝ))) := by
    have h1 := hu.hasSum.tendsto_sum_nat
    rw [pfun]
    simpa using h1.sub herrlim
  have h2 := hAB.tendsto_sum_nat
  have huniq := tendsto_nhds_unique h2 hlim
  have hAB2 : HasSum
      (fun n : ℕ => chapter9OddHarmonic (n + 1) * t ^ n
        - chapter9OddHarmonic (n + 1) * t ^ (n + 1))
      (∑' n, t ^ n / (((2 * n + 1 : ℕ)) : ℝ)) := by
    rw [← huniq]
    exact hAB
  have hval : (∑' n, chapter9OddHarmonic (n + 1) * t ^ n)
      - t * (∑' n, chapter9OddHarmonic (n + 1) * t ^ n)
      = ∑' n, t ^ n / (((2 * n + 1 : ℕ)) : ℝ) := HasSum.unique hAB hAB2
  have h1t : (1 : ℝ) - t ≠ 0 := by
    have := abs_lt.mp ht
    linarith [ne_of_gt (show (0 : ℝ) < 1 - t by linarith)]
  have hfin : (∑' n, chapter9OddHarmonic (n + 1) * t ^ n)
      = (∑' n, t ^ n / (((2 * n + 1 : ℕ)) : ℝ)) / (1 - t) := by
    rw [eq_div_iff h1t]
    linear_combination hval
  rw [hfin] at hT
  exact hT

private lemma Y_hasDerivAt {R x : ℝ} (hR0 : 0 < R) (hR1 : R < 1)
    (hx : x ∈ Set.Ioo (-R) R) :
    HasDerivAt (fun x : ℝ => x / (2 - x)) (2 / (2 - x) ^ 2) x := by
  have hxR : x < R := (Set.mem_Ioo.mp hx).2
  have h2x : (2 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
  have hnum := hasDerivAt_id' x
  have hden : HasDerivAt (fun x : ℝ => 2 - x) (-1) x :=
    (hasDerivAt_id' x).const_sub 2
  have h := hnum.div hden h2x
  have hval : (1 * (2 - x) - x * -1) / (2 - x) ^ 2 = 2 / (2 - x) ^ 2 := by
    ring
  rw [hval] at h
  exact h

private lemma Y_abs_le {R x : ℝ} (hR0 : 0 < R) (hR1 : R < 1)
    (hx : x ∈ Set.Ioo (-R) R) :
    ‖x / (2 - x)‖ ≤ R / (2 - R) := by
  have hxR : x < R := (Set.mem_Ioo.mp hx).2
  have h2x : (0 : ℝ) < 2 - x := by linarith
  have h2R : (0 : ℝ) < 2 - R := by linarith
  have hle : (2 : ℝ) - R ≤ 2 - x := by linarith
  have hinv : 1 / (2 - x) ≤ 1 / (2 - R) :=
    one_div_le_one_div_of_le h2R hle
  have hyR2 : |x| ≤ R := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hx))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h2x]
  calc |x| / (2 - x) = |x| * (1 / (2 - x)) := by ring
    _ ≤ R * (1 / (2 - R)) :=
        mul_le_mul hyR2 hinv (div_nonneg zero_le_one h2x.le) hR0.le
    _ = R / (2 - R) := by ring

private lemma Yderiv_abs_le {R x : ℝ} (hR0 : 0 < R) (hR1 : R < 1)
    (hx : x ∈ Set.Ioo (-R) R) :
    ‖2 / (2 - x) ^ 2‖ ≤ 2 / (2 - R) ^ 2 := by
  have hxR : x < R := (Set.mem_Ioo.mp hx).2
  have h2x : (0 : ℝ) < 2 - x := by linarith
  have h2R : (0 : ℝ) < 2 - R := by linarith
  have hle : (2 : ℝ) - R ≤ 2 - x := by linarith
  have hsq : (2 - R) ^ 2 ≤ (2 - x) ^ 2 :=
    pow_le_pow_left₀ h2R.le hle 2
  have hnn : (0 : ℝ) ≤ 2 / (2 - x) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact div_le_div_of_nonneg_left zero_le_two (pow_pos h2R 2) hsq

private lemma hasDerivAt_Ffun {x0 R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) (hx0 : |x0| < R) :
    HasDerivAt (fun x => chapter9Entry8F (x / (2 - x)))
      (∑' n, chapter9OddHarmonic (n + 1) * (x0 / (2 - x0)) ^ (2 * n)
        * (2 / (2 - x0) ^ 2)) x0 := by
  have hmem : x0 ∈ Set.Ioo (-R) R := Set.mem_Ioo.mpr (abs_lt.mp hx0)
  have h2R : (0 : ℝ) < 2 - R := by linarith
  have hSnn : (0 : ℝ) ≤ R / (2 - R) := div_nonneg hR0.le h2R.le
  have hS1 : R / (2 - R) < 1 := by
    rw [div_lt_one h2R]
    linarith
  have hnormS : ‖(R / (2 - R) : ℝ)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hSnn]
  have hsumu : Summable
      (fun n : ℕ => ((n : ℝ) + 1) * (R / (2 - R)) ^ (2 * n)
        * (2 / (2 - R) ^ 2)) := by
    have e : (fun n : ℕ => ((n : ℝ) + 1) * (R / (2 - R)) ^ (2 * n)
          * (2 / (2 - R) ^ 2))
        = fun n : ℕ => (2 / (2 - R) ^ 2)
          * (((n : ℝ) + 1) * ((R / (2 - R)) ^ 2) ^ n) := by
      funext n
      rw [← pow_mul]
      ring
    rw [e]
    apply Summable.mul_left
    have hSS : ‖(((R / (2 - R)) ^ 2 : ℝ))‖ < 1 := by
      have hsq : (R / (2 - R)) ^ 2 < 1 := by nlinarith [hS1, hSnn]
      have hnn : (0 : ℝ) ≤ (R / (2 - R)) ^ 2 := by positivity
      rwa [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact summable_n1_mul_pow hSS
  have hDne : ∀ n : ℕ, (((2 * n + 1 : ℕ)) : ℝ) ≠ 0 := fun n =>
    Nat.cast_ne_zero.mpr (by omega)
  have hderiv1 : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-R) R,
      HasDerivAt
        (fun x => chapter9OddHarmonic (n + 1) * (x / (2 - x)) ^ (2 * n + 1)
          / (((2 * n + 1 : ℕ)) : ℝ))
        (chapter9OddHarmonic (n + 1) * (y / (2 - y)) ^ (2 * n)
          * (2 / (2 - y) ^ 2)) y := by
    intro n y hy
    have h2 := (((Y_hasDerivAt hR0 hR1 hy).pow (2 * n + 1)).const_mul
      (chapter9OddHarmonic (n + 1))).div_const (((2 * n + 1 : ℕ)) : ℝ)
    simp only [Pi.pow_apply] at h2
    rw [Nat.add_sub_cancel] at h2
    have hval : chapter9OddHarmonic (n + 1)
          * (↑(2 * n + 1) * (y / (2 - y)) ^ (2 * n) * (2 / (2 - y) ^ 2))
          / (((2 * n + 1 : ℕ)) : ℝ)
        = chapter9OddHarmonic (n + 1) * (y / (2 - y)) ^ (2 * n)
          * (2 / (2 - y) ^ 2) := by
      have hD := hDne n
      field_simp
    rw [hval] at h2
    exact h2
  have hbound : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-R) R,
      ‖chapter9OddHarmonic (n + 1) * (y / (2 - y)) ^ (2 * n)
        * (2 / (2 - y) ^ 2)‖
        ≤ ((n : ℝ) + 1) * (R / (2 - R)) ^ (2 * n) * (2 / (2 - R) ^ 2) := by
    intro n y hy
    have hYb := Y_abs_le hR0 hR1 hy
    have hYd := Yderiv_abs_le hR0 hR1 hy
    have hHn : ‖chapter9OddHarmonic (n + 1)‖ ≤ (n : ℝ) + 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (oddHarmonic_nonneg _)]
      calc chapter9OddHarmonic (n + 1) ≤ (((n + 1 : ℕ)) : ℝ) := by
            exact_mod_cast oddHarmonic_le (n + 1)
        _ = (n : ℝ) + 1 := by push_cast; ring
    have hYp : ‖y / (2 - y)‖ ^ (2 * n) ≤ (R / (2 - R)) ^ (2 * n) :=
      pow_le_pow_left₀ (norm_nonneg _) hYb _
    rw [norm_mul, norm_mul, norm_pow]
    have hinner : ‖chapter9OddHarmonic (n + 1)‖ * ‖y / (2 - y)‖ ^ (2 * n)
        ≤ ((n : ℝ) + 1) * (R / (2 - R)) ^ (2 * n) :=
      mul_le_mul hHn hYp (by positivity) (by positivity)
    exact mul_le_mul hinner hYd (by positivity)
      (mul_nonneg (by positivity) (pow_nonneg hSnn _))
  have hY1 : |x0 / (2 - x0)| < 1 := by
    have h := Y_abs_le hR0 hR1 hmem
    rw [Real.norm_eq_abs] at h
    exact lt_of_le_of_lt h hS1
  have hsum0 : Summable
      (fun n : ℕ => chapter9OddHarmonic (n + 1) * (x0 / (2 - x0)) ^ (2 * n + 1)
        / (((2 * n + 1 : ℕ)) : ℝ)) :=
    summable_FTerm hY1
  have hmain := hasDerivAt_tsum_of_isPreconnected hsumu isOpen_Ioo
    (convex_Ioo (-R) R).isPreconnected hderiv1 hbound hmem hsum0 hmem
  have efun : (fun z => ∑' n, chapter9OddHarmonic (n + 1) * (z / (2 - z)) ^ (2 * n + 1)
        / (((2 * n + 1 : ℕ)) : ℝ))
      = (fun x => chapter9Entry8F (x / (2 - x))) := by
    funext z
    simp only [chapter9Entry8F, chapter9Entry8FTerm]
  rw [efun] at hmain
  exact hmain

private lemma hasDerivAt_Dfun {x0 R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) (hx0 : |x0| < R) :
    HasDerivAt (fun x => chapter9Entry8Dilog x)
      (∑' n, x0 ^ n / (((n + 1 : ℕ)) : ℝ)) x0 := by
  have hmem : x0 ∈ Set.Ioo (-R) R := Set.mem_Ioo.mpr (abs_lt.mp hx0)
  have hR1' : |R| < 1 := by rwa [abs_of_pos hR0]
  have hsumv : Summable (fun n : ℕ => R ^ n) :=
    summable_geometric_of_abs_lt_one hR1'
  have hDne : ∀ n : ℕ, (((n + 1 : ℕ)) : ℝ) ≠ 0 := fun n =>
    Nat.cast_ne_zero.mpr (by omega)
  have hderiv1 : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-R) R,
      HasDerivAt (fun x => x ^ (n + 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2))
        (y ^ n / (((n + 1 : ℕ)) : ℝ)) y := by
    intro n y hy
    have h1 := ((hasDerivAt_id' y).pow (n + 1)).div_const
      ((((n + 1 : ℕ)) : ℝ) ^ 2)
    simp only [Pi.pow_apply] at h1
    rw [Nat.add_sub_cancel] at h1
    have hval : (↑(n + 1) * y ^ n * 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2)
        = y ^ n / (((n + 1 : ℕ)) : ℝ) := by
      have hD := hDne n
      field_simp
    rw [hval] at h1
    exact h1
  have hbound : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-R) R,
      ‖y ^ n / (((n + 1 : ℕ)) : ℝ)‖ ≤ R ^ n := by
    intro n y hy
    have hyR : |y| ≤ R := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hy))
    have hD1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hnn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hDn : ‖(((n + 1 : ℕ)) : ℝ)‖ = (((n + 1 : ℕ)) : ℝ) := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg hnn
    have hYp : |y| ^ n ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg _) hyR n
    simp only [norm_div, norm_pow, Real.norm_eq_abs, hDn]
    calc |y| ^ n / ((n + 1 : ℕ) : ℝ) ≤ R ^ n / ((n + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hYp hnn
      _ ≤ R ^ n := div_le_self (by positivity) hD1
  have hx01 : |x0| < 1 := lt_trans hx0 hR1
  have hsum0 : Summable
      (fun n : ℕ => x0 ^ (n + 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
    summable_dilogTerm hx01
  have hmain := hasDerivAt_tsum_of_isPreconnected hsumv isOpen_Ioo
    (convex_Ioo (-R) R).isPreconnected hderiv1 hbound hmem hsum0 hmem
  have efun : (fun z => ∑' n, z ^ (n + 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2))
      = (fun x => chapter9Entry8Dilog x) := by
    funext z
    simp only [chapter9Entry8Dilog, chapter9Entry8DilogTerm]
  rw [efun] at hmain
  exact hmain

private lemma hasDerivAt_Gfun {x0 R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) (hx0 : |x0| < R) :
    HasDerivAt (fun x => (1 / 8 : ℝ) * (Real.log (1 - x)) ^ 2
        + (1 / 2 : ℝ) * chapter9Entry8Dilog x)
      ((1 / 8 : ℝ) * ((-1 / (1 - x0)) * Real.log (1 - x0)
        + Real.log (1 - x0) * (-1 / (1 - x0)))
        + (1 / 2 : ℝ) * (∑' n, x0 ^ n / (((n + 1 : ℕ)) : ℝ))) x0 := by
  have hx01 : x0 < 1 := by
    have h := abs_lt.mp (lt_trans hx0 hR1)
    linarith
  have h1t : (0 : ℝ) < 1 - x0 := by linarith
  have hL' : HasDerivAt (fun x => Real.log (1 - x)) (-1 / (1 - x0)) x0 := by
    have h1mx : HasDerivAt (fun x : ℝ => 1 - x) (-1) x0 :=
      (hasDerivAt_id' x0).const_sub 1
    have hlog : HasDerivAt Real.log (1 - x0)⁻¹ (1 - x0) :=
      Real.hasDerivAt_log (ne_of_gt h1t)
    have h := hlog.comp x0 h1mx
    have hval : (1 - x0)⁻¹ * -1 = -1 / (1 - x0) := by
      rw [div_eq_mul_inv]
      ring
    rw [hval] at h
    exact h
  have hL2 := hL'.mul hL'
  have hG1 := hL2.const_mul (1 / 8 : ℝ)
  have hD := (hasDerivAt_Dfun hR0 hR1 hx0).const_mul (1 / 2 : ℝ)
  have hG := hG1.add hD
  have efunG : ((fun y : ℝ => (1 / 8 : ℝ)
          * (((fun x => Real.log (1 - x)) * (fun x => Real.log (1 - x))) y))
        + (fun y : ℝ => (1 / 2 : ℝ) * chapter9Entry8Dilog y))
      = (fun x : ℝ => (1 / 8 : ℝ) * (Real.log (1 - x)) ^ 2
          + (1 / 2 : ℝ) * chapter9Entry8Dilog x) := by
    funext x
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rw [efunG] at hG
  exact hG

private lemma derivEq_ne {x0 : ℝ} (hx0 : |x0| < 1) (hx00 : x0 ≠ 0) :
    (∑' n, chapter9OddHarmonic (n + 1) * (x0 / (2 - x0)) ^ (2 * n)
      * (2 / (2 - x0) ^ 2))
    = (1 / 8 : ℝ) * ((-1 / (1 - x0)) * Real.log (1 - x0)
      + Real.log (1 - x0) * (-1 / (1 - x0)))
      + (1 / 2 : ℝ) * (∑' n, x0 ^ n / (((n + 1 : ℕ)) : ℝ)) := by
  have hx1 : x0 < 1 := by
    have h := abs_lt.mp hx0
    linarith
  have h2x : (2 : ℝ) - x0 ≠ 0 := ne_of_gt (by linarith)
  have h1x : (1 : ℝ) - x0 ≠ 0 := ne_of_gt (by linarith)
  have h2xpos : (0 : ℝ) < 2 - x0 := by linarith
  have hY0lt : |x0 / (2 - x0)| < 1 := by
    rw [abs_div, abs_of_pos h2xpos, div_lt_one h2xpos]
    calc |x0| < 1 := hx0
      _ < 2 - x0 := by linarith
  have hY0ne : x0 / (2 - x0) ≠ 0 := div_ne_zero hx00 h2x
  have hY0sq : |(x0 / (2 - x0)) ^ 2| < 1 :=
    abs_sq_lt_one_of_abs_lt_one hY0lt
  have hD' : (∑' n, x0 ^ n / (((n + 1 : ℕ)) : ℝ))
      = -Real.log (1 - x0) / x0 := by
    have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := x0) hx0
    have h2 := hlog.div_const x0
    have e : (fun n : ℕ => (x0 ^ (n + 1) / ((n : ℝ) + 1)) / x0)
        = (fun n : ℕ => x0 ^ n / (((n + 1 : ℕ)) : ℝ)) := by
      funext n
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by
        push_cast
        ring
      have hn1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
      rw [hcast]
      field_simp
      ring
    rw [e] at h2
    exact h2.tsum_eq
  have hFfac : (∑' n, chapter9OddHarmonic (n + 1) * (x0 / (2 - x0)) ^ (2 * n)
        * (2 / (2 - x0) ^ 2))
      = (∑' n, chapter9OddHarmonic (n + 1) * ((x0 / (2 - x0)) ^ 2) ^ n)
        * (2 / (2 - x0) ^ 2) := by
    have ef : (fun n : ℕ => chapter9OddHarmonic (n + 1) * (x0 / (2 - x0)) ^ (2 * n)
          * (2 / (2 - x0) ^ 2))
        = (fun n : ℕ => (chapter9OddHarmonic (n + 1)
          * ((x0 / (2 - x0)) ^ 2) ^ n) * (2 / (2 - x0) ^ 2)) := by
      funext n
      rw [← pow_mul]
    rw [ef, tsum_mul_right]
  have hTval : (∑' n, chapter9OddHarmonic (n + 1) * ((x0 / (2 - x0)) ^ 2) ^ n)
      = (∑' j, ((x0 / (2 - x0)) ^ 2) ^ j / (((2 * j + 1 : ℕ)) : ℝ))
        / (1 - (x0 / (2 - x0)) ^ 2) :=
    (hasSum_T_eq (t := (x0 / (2 - x0)) ^ 2) hY0sq).tsum_eq
  have hUval : (∑' j, ((x0 / (2 - x0)) ^ 2) ^ j / (((2 * j + 1 : ℕ)) : ℝ))
      = (∑' j, (x0 / (2 - x0)) ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ))
        / (x0 / (2 - x0)) := by
    have hSU : (∑' j, (x0 / (2 - x0)) ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ))
        = (x0 / (2 - x0))
          * (∑' j, ((x0 / (2 - x0)) ^ 2) ^ j / (((2 * j + 1 : ℕ)) : ℝ)) := by
      have es : (fun j : ℕ => (x0 / (2 - x0)) ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ))
          = (fun j : ℕ => (x0 / (2 - x0))
            * (((x0 / (2 - x0)) ^ 2) ^ j / (((2 * j + 1 : ℕ)) : ℝ))) := by
        funext j
        rw [← pow_mul, pow_succ']
        ring
      rw [es, tsum_mul_left]
    rw [hSU, mul_div_cancel_left₀ _ hY0ne]
  have h1pY : (1 : ℝ) + x0 / (2 - x0) = 2 / (2 - x0) := by
    calc (1 : ℝ) + x0 / (2 - x0)
        = (2 - x0) / (2 - x0) + x0 / (2 - x0) := by rw [div_self h2x]
      _ = ((2 - x0) + x0) / (2 - x0) := by rw [add_div]
      _ = 2 / (2 - x0) := by rw [show (2 : ℝ) - x0 + x0 = 2 by ring]
  have h1mY : (1 : ℝ) - x0 / (2 - x0) = 2 * (1 - x0) / (2 - x0) := by
    calc (1 : ℝ) - x0 / (2 - x0)
        = (2 - x0) / (2 - x0) - x0 / (2 - x0) := by rw [div_self h2x]
      _ = ((2 - x0) - x0) / (2 - x0) := by rw [← sub_div]
      _ = 2 * (1 - x0) / (2 - x0) := by
          rw [show (2 : ℝ) - x0 - x0 = 2 * (1 - x0) by ring]
  have hSclosed : (∑' j, (x0 / (2 - x0)) ^ (2 * j + 1) / (((2 * j + 1 : ℕ)) : ℝ))
      = -Real.log (1 - x0) / 2 := by
    have hSval := (hasSum_odd_log hY0lt).tsum_eq
    rw [hSval, h1pY, h1mY]
    have e1 : Real.log (2 / (2 - x0)) = Real.log 2 - Real.log (2 - x0) :=
      Real.log_div (by norm_num) h2x
    have e2 : Real.log (2 * (1 - x0) / (2 - x0))
        = Real.log 2 + Real.log (1 - x0) - Real.log (2 - x0) := by
      rw [Real.log_div (mul_ne_zero (by norm_num) h1x) h2x,
        Real.log_mul (by norm_num) h1x]
    rw [e1, e2]
    ring
  have h1mY2 : 1 - (x0 / (2 - x0)) ^ 2 = 4 * (1 - x0) / (2 - x0) ^ 2 := by
    have e : (x0 / (2 - x0)) ^ 2 = x0 ^ 2 / (2 - x0) ^ 2 := div_pow _ _ _
    rw [e]
    calc 1 - x0 ^ 2 / (2 - x0) ^ 2
        = (2 - x0) ^ 2 / (2 - x0) ^ 2 - x0 ^ 2 / (2 - x0) ^ 2 := by
          rw [div_self (pow_ne_zero 2 h2x)]
      _ = ((2 - x0) ^ 2 - x0 ^ 2) / (2 - x0) ^ 2 := by rw [sub_div]
      _ = 4 * (1 - x0) / (2 - x0) ^ 2 := by
          rw [show (2 - x0) ^ 2 - x0 ^ 2 = 4 * (1 - x0) by ring]
  rw [hFfac, hTval, hUval, hSclosed, hD', h1mY2]
  field_simp
  ring

private lemma derivEq_zero :
    (∑' n, chapter9OddHarmonic (n + 1) * (0 / (2 - 0)) ^ (2 * n)
      * (2 / (2 - 0) ^ 2))
    = (1 / 8 : ℝ) * ((-1 / (1 - 0)) * Real.log (1 - 0)
      + Real.log (1 - 0) * (-1 / (1 - 0)))
      + (1 / 2 : ℝ) * (∑' n, (0 : ℝ) ^ n / (((n + 1 : ℕ)) : ℝ)) := by
  have htsumF : (∑' n, chapter9OddHarmonic (n + 1) * (0 / (2 - 0)) ^ (2 * n)
        * (2 / (2 - 0) ^ 2)) = 1 / 2 := by
    have ef : (fun n : ℕ => chapter9OddHarmonic (n + 1) * (0 / (2 - 0)) ^ (2 * n)
          * (2 / (2 - 0) ^ 2))
        = (fun n : ℕ => if n = 0 then (1 / 2 : ℝ) else 0) := by
      funext n
      have h00 : (0 : ℝ) / (2 - 0) = 0 := zero_div _
      by_cases hn : n = 0
      · subst hn
        rw [ite_eq_left rfl]
        norm_num [h00, chapter9OddHarmonic, Finset.sum_range_one]
      · rw [ite_eq_right hn, h00, zero_pow (by omega : 2 * n ≠ 0)]
        ring
    rw [ef]
    exact (hasSum_ite_eq 0 (1 / 2 : ℝ)).tsum_eq
  have htsumD : (∑' n, (0 : ℝ) ^ n / (((n + 1 : ℕ)) : ℝ)) = 1 := by
    have eD : (fun n : ℕ => (0 : ℝ) ^ n / (((n + 1 : ℕ)) : ℝ))
        = (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) := by
      funext n
      by_cases hn : n = 0
      · subst hn
        rw [ite_eq_left rfl]
        norm_num
      · rw [ite_eq_right hn, zero_pow hn]
        exact zero_div _
    rw [eD]
    exact (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq
  rw [htsumF, htsumD]
  norm_num [Real.log_one]

/-- **Ramanujan's odd harmonic series identity.** Let $x$ be a real number with $|x| < 1$. For
$n \ge 0$ put $h_n = 1 + \frac{1}{3} + \cdots + \frac{1}{2n+1}$, for real $y$ let
$F(y) = \sum_{n \ge 0} \frac{h_n}{2n+1} y^{2n+1}$, and let
$\operatorname{Li}_2(x) = \sum_{k \ge 1} \frac{x^k}{k^2}$. Then $1 - x > 0$, $2 - x \ne 0$ and
$|x/(2-x)| < 1$; the series defining $F(x/(2-x))$ and the series defining
$\operatorname{Li}_2(x)$ are both summable; and

$$F\left(\frac{x}{2-x}\right) = \frac{(\log(1-x))^2}{8} + \frac{\operatorname{Li}_2(x)}{2}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9,
Entry 8, pp. 249–250.
Proves `Wanted` entry `ramanujan_part1_ch9_entry8_arcsin`.
-/
theorem ramanujan_part1_ch9_entry8_arcsin (x : ℝ) (hx : |x| < 1) :
    0 < 1 - x ∧
      2 - x ≠ 0 ∧
      |x / (2 - x)| < 1 ∧
      Summable (chapter9Entry8FTerm (x / (2 - x))) ∧
      Summable (chapter9Entry8DilogTerm x) ∧
      chapter9Entry8F (x / (2 - x)) =
        (1 / 8 : ℝ) * Real.log (1 - x) ^ 2 +
          (1 / 2 : ℝ) * chapter9Entry8Dilog x := by
  have hx1 : x < 1 := by
    have h := abs_lt.mp hx
    linarith
  have h2xpos : (0 : ℝ) < 2 - x := by linarith
  have h2x : (2 : ℝ) - x ≠ 0 := ne_of_gt h2xpos
  have hY : |x / (2 - x)| < 1 := by
    rw [abs_div, abs_of_pos h2xpos, div_lt_one h2xpos]
    calc |x| < 1 := hx
      _ < 2 - x := by linarith
  refine ⟨by linarith, h2x, hY, summable_FTerm hY, summable_dilogTerm hx, ?_⟩
  have e0 : chapter9Entry8F ((0 : ℝ) / (2 - 0)) = 0 := by
    have ef : (fun n : ℕ => chapter9Entry8FTerm ((0 : ℝ) / (2 - 0)) n)
        = fun _ => (0 : ℝ) := by
      funext n
      show chapter9OddHarmonic (n + 1) * ((0 : ℝ) / (2 - 0)) ^ (2 * n + 1)
        / (((2 * n + 1 : ℕ)) : ℝ) = 0
      rw [zero_div, zero_pow (by omega : 2 * n + 1 ≠ 0)]
      ring
    show (∑' n, chapter9Entry8FTerm ((0 : ℝ) / (2 - 0)) n) = 0
    rw [ef]
    exact tsum_zero
  have e1 : chapter9Entry8Dilog (0 : ℝ) = 0 := by
    have ef : (fun n : ℕ => chapter9Entry8DilogTerm (0 : ℝ) n)
        = fun _ => (0 : ℝ) := by
      funext n
      show (0 : ℝ) ^ (n + 1) / ((((n + 1 : ℕ)) : ℝ) ^ 2) = 0
      rw [zero_pow (by omega : n + 1 ≠ 0)]
      exact zero_div _
    show (∑' n, chapter9Entry8DilogTerm (0 : ℝ) n) = 0
    rw [ef]
    exact tsum_zero
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt ((fun x => chapter9Entry8F (x / (2 - x)))
        - (fun x => (1 / 8 : ℝ) * Real.log (1 - x) ^ 2
          + (1 / 2 : ℝ) * chapter9Entry8Dilog x))
        ((fun _ : ℝ => (0 : ℝ)) t) t := by
    intro t ht
    have htat : |t| < 1 := by
      rcases le_total 0 x with h0x | hx0
      · rw [Set.uIcc_of_le h0x] at ht
        have ht1 : t ≤ x := (Set.mem_Icc.mp ht).2
        have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
        rw [abs_of_nonneg ht0]
        calc t ≤ x := ht1
          _ ≤ |x| := le_abs_self x
          _ < 1 := hx
      · rw [Set.uIcc_of_ge hx0] at ht
        have ht1 : x ≤ t := (Set.mem_Icc.mp ht).1
        have ht0 : t ≤ 0 := (Set.mem_Icc.mp ht).2
        rw [abs_of_nonpos ht0]
        calc -t ≤ -x := neg_le_neg ht1
          _ = |x| := (abs_of_nonpos hx0).symm
          _ < 1 := hx
    have hR0 : (0 : ℝ) < (|t| + 1) / 2 := by
      have h := abs_nonneg t
      linarith
    have hR1 : (|t| + 1) / 2 < 1 := by linarith
    have htR : |t| < (|t| + 1) / 2 := by linarith
    have hF := hasDerivAt_Ffun hR0 hR1 htR
    have hG := hasDerivAt_Gfun hR0 hR1 htR
    have hsub := hF.sub hG
    have hFG : (∑' n, chapter9OddHarmonic (n + 1) * (t / (2 - t)) ^ (2 * n)
          * (2 / (2 - t) ^ 2))
        = (1 / 8 : ℝ) * ((-1 / (1 - t)) * Real.log (1 - t)
          + Real.log (1 - t) * (-1 / (1 - t)))
          + (1 / 2 : ℝ) * (∑' n, t ^ n / (((n + 1 : ℕ)) : ℝ)) := by
      by_cases ht0 : t = 0
      · subst ht0
        exact derivEq_zero
      · exact derivEq_ne htat ht0
    rw [hFG, sub_self] at hsub
    exact hsub
  have hint : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume
      (0 : ℝ) x :=
    intervalIntegrable_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hint0 : (∫ y : ℝ in (0 : ℝ)..x, (fun _ : ℝ => (0 : ℝ)) y) = 0 := by
    simp
  rw [hint0] at hftc
  have hD0 : ((fun x => chapter9Entry8F (x / (2 - x)))
      - (fun x => (1 / 8 : ℝ) * Real.log (1 - x) ^ 2
        + (1 / 2 : ℝ) * chapter9Entry8Dilog x)) 0 = 0 := by
    show chapter9Entry8F ((0 : ℝ) / (2 - 0))
      - ((1 / 8 : ℝ) * Real.log (1 - 0) ^ 2
        + (1 / 2 : ℝ) * chapter9Entry8Dilog 0) = 0
    rw [e0, e1]
    simp [Real.log_one]
  have hDx : ((fun x => chapter9Entry8F (x / (2 - x)))
      - (fun x => (1 / 8 : ℝ) * Real.log (1 - x) ^ 2
        + (1 / 2 : ℝ) * chapter9Entry8Dilog x)) x = 0 := by
    linarith [hftc, hD0]
  simp only [Pi.sub_apply] at hDx
  exact sub_eq_zero.mp hDx

end

end Entry8Arcsin

end MathlibExt.Analysis.Ramanujan.Part1Ch9
