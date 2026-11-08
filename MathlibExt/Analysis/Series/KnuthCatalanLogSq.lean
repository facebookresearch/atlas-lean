/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Normed.Group.FunctionSeries

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section

open scoped BigOperators

namespace MetaMathlibExt

/-! # Knuth Catalan log-squared generating function -/

private lemma cb_succ_real (m : ℕ) :
    (Nat.centralBinom (m + 1) : ℝ) = 2 * (2 * (m : ℝ) + 1) / ((m : ℝ) + 1) *
      (Nat.centralBinom m : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have hcast : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
      = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
    exact_mod_cast h
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [hcast]

private lemma catalan_cast (n : ℕ) :
    (catalan n : ℝ) = (Nat.centralBinom n : ℝ) / ((n : ℝ) + 1) := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hcast : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
    exact_mod_cast h
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [hcast]

private lemma cat_le_four_pow (n : ℕ) : (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by
  have h := Nat.centralBinom_le_four_pow n
  have h2 := succ_mul_catalan_eq_centralBinom n
  rw [← h2] at h
  have h3 : catalan n ≤ 4 ^ n := by
    calc catalan n = 1 * catalan n := by rw [one_mul]
      _ ≤ (n + 1) * catalan n := by
        gcongr
        omega
      _ ≤ 4 ^ n := h
  exact_mod_cast h3

private lemma catalan_succ_eq (n : ℕ) : (catalan (n + 1) : ℝ)
    = (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2)) * (catalan n : ℝ) := by
  have e1 := catalan_cast (n + 1)
  have e2 := catalan_cast n
  have eN : ((((n + 1 : ℕ))) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have h2 : (Nat.centralBinom (n + 1) : ℝ)
      = (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) * (Nat.centralBinom n : ℝ) :=
    cb_succ_real n
  have hne1 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hne2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [e1, e2, eN, h2]
  field_simp

private lemma catalan_succ_le (n : ℕ) : (catalan (n + 1) : ℝ) ≤ 4 * (catalan n : ℝ) := by
  rw [catalan_succ_eq]
  have hnn : (0 : ℝ) ≤ catalan n := by positivity
  have hfac : (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2)) ≤ 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact mul_le_mul_of_nonneg_right hfac hnn

private lemma summable_cat_norm (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n => ‖(catalan n : ℝ) * x ^ n‖) := by
  have hq : (4 : ℝ) * |x| < 1 := by linarith [hx]
  have hnn : (0 : ℝ) ≤ 4 * |x| := by positivity
  have hgeom := summable_geometric_of_lt_one hnn hq
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeom
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (catalan n : ℝ))]
  calc (catalan n : ℝ) * |x| ^ n
      ≤ (4 : ℝ) ^ n * |x| ^ n :=
        mul_le_mul_of_nonneg_right (cat_le_four_pow n) (pow_nonneg (abs_nonneg x) n)
    _ = (4 * |x|) ^ n := by ring

private lemma summable_cat (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n => (catalan n : ℝ) * x ^ n) :=
  (summable_cat_norm x hx).of_norm

/-- Each consecutive pair of terms is nonnegative inside the closed radius. -/
private lemma pair_nonneg (x : ℝ) (hx : |x| ≤ 1 / 4) (k : ℕ) :
    (0 : ℝ) ≤ (catalan (2 * k) : ℝ) * x ^ (2 * k)
      + (catalan (2 * k + 1) : ℝ) * x ^ (2 * k + 1) := by
  have h4 : 4 * |x| ≤ 1 := by linarith [hx]
  have hle : (catalan (2 * k + 1) : ℝ) ≤ 4 * (catalan (2 * k) : ℝ) := by
    have h := catalan_succ_le (2 * k)
    rwa [show 2 * k + 1 = (2 * k) + 1 from rfl] at h
  have hnn : (0 : ℝ) ≤ (catalan (2 * k) : ℝ) := by positivity
  have hnn1 : (0 : ℝ) ≤ (catalan (2 * k + 1) : ℝ) := by positivity
  have hsq : (0 : ℝ) ≤ x ^ (2 * k) := by
    have e : x ^ (2 * k) = (x ^ k) ^ 2 := by ring
    rw [e]
    exact sq_nonneg _
  have hfactor : (catalan (2 * k) : ℝ) * x ^ (2 * k)
        + (catalan (2 * k + 1) : ℝ) * x ^ (2 * k + 1)
      = x ^ (2 * k) * ((catalan (2 * k) : ℝ) + (catalan (2 * k + 1) : ℝ) * x) := by
    ring
  rw [hfactor]
  apply mul_nonneg hsq
  have h1 : (catalan (2 * k + 1) : ℝ) * x ≥ -((catalan (2 * k + 1) : ℝ) * |x|) := by
    calc (catalan (2 * k + 1) : ℝ) * x
        ≥ (catalan (2 * k + 1) : ℝ) * (-|x|) := by
          apply mul_le_mul_of_nonneg_left _ hnn1
          exact neg_abs_le x
      _ = -((catalan (2 * k + 1) : ℝ) * |x|) := by ring
  have h2 : (catalan (2 * k + 1) : ℝ) * |x| ≤ 4 * (catalan (2 * k) : ℝ) * |x| := by
    have h := mul_le_mul_of_nonneg_right hle (abs_nonneg x)
    linarith [h]
  have hside : (catalan (2 * k) : ℝ) + (catalan (2 * k + 1) : ℝ) * x
      ≥ (catalan (2 * k) : ℝ) * (1 - 4 * |x|) := by
    have h3 : (catalan (2 * k) : ℝ) * (1 - 4 * |x|)
        = (catalan (2 * k) : ℝ) - 4 * (catalan (2 * k) : ℝ) * |x| := by ring
    linarith [h1, h2, h3]
  have hpos : (0 : ℝ) ≤ (catalan (2 * k) : ℝ) * (1 - 4 * |x|) :=
    mul_nonneg hnn (by linarith [h4])
  linarith [hside, hpos]

/-- The Catalan generating function is positive inside the radius. -/
private lemma catalan_tsum_pos (x : ℝ) (hx : |x| < 1 / 4) :
    0 < ∑' n, (catalan n : ℝ) * x ^ n := by
  have hsum := summable_cat x hx
  have hE : ∀ K, (1 : ℝ) + x ≤ ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * x ^ n := by
    intro K
    induction K with
    | zero =>
      have e0 : 2 * (0 + 1) = 2 := by norm_num
      rw [e0]
      have h2 : ∑ n ∈ Finset.range 2, (catalan n : ℝ) * x ^ n = 1 + x := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp [catalan_zero, catalan_one]
      rw [h2]
    | succ K ih =>
      have hstep : ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * x ^ n
          ≤ ∑ n ∈ Finset.range (2 * (K + 1 + 1)), (catalan n : ℝ) * x ^ n := by
        have e : 2 * (K + 1 + 1) = 2 * (K + 1) + 1 + 1 := by omega
        rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
        have hp := pair_nonneg x (le_of_lt hx) (K + 1)
        linarith [hp]
      exact le_trans ih hstep
  have hPr : ∀ N, 1 ≤ N → 1 - |x| ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * x ^ n := by
    intro N hN
    have hx1 : (1 : ℝ) + x ≥ 1 - |x| := by linarith [neg_abs_le x]
    rcases Nat.even_or_odd N with hE | hO
    · obtain ⟨K, rfl⟩ := hE
      have eKK : K + K = 2 * K := by omega
      have hK : 1 ≤ K := by omega
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have h := hE K'
      rw [show K' + 1 + (K' + 1) = 2 * (K' + 1) by omega]
      linarith [h, hx1]
    · obtain ⟨K, rfl⟩ := hO
      by_cases hK : K = 0
      · subst hK
        have e : 2 * 0 + 1 = 1 := by norm_num
        rw [e, Finset.sum_range_one]
        simp only [catalan_zero, Nat.cast_one, pow_zero, mul_one]
        linarith [abs_nonneg x]
      · have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
        have h1 : ∑ n ∈ Finset.range (2 * K), (catalan n : ℝ) * x ^ n
            ≤ ∑ n ∈ Finset.range (2 * K + 1), (catalan n : ℝ) * x ^ n := by
          rw [Finset.sum_range_succ]
          have hnn : (0 : ℝ) ≤ (catalan (2 * K) : ℝ) * x ^ (2 * K) := by
            apply mul_nonneg (by positivity)
            have e : x ^ (2 * K) = (x ^ K) ^ 2 := by ring
            rw [e]
            exact sq_nonneg _
          linarith [hnn]
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        have h2 := hE K'
        linarith [h1, h2, hx1]
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (catalan n : ℝ) * x ^ n) Filter.atTop
      (nhds (∑' n, (catalan n : ℝ) * x ^ n)) :=
    (Summable.hasSum_iff_tendsto_nat hsum).mp hsum.hasSum
  have hev : ∀ᶠ N in Filter.atTop, (1 : ℝ) - |x| ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * x ^ n :=
    Filter.eventually_atTop.mpr ⟨1, fun N hN => hPr N hN⟩
  have hge := ge_of_tendsto hlim hev
  have hrpos : (0 : ℝ) < 1 - |x| := by linarith [hx]
  linarith [hge, hrpos]

/-- Convolution of Catalan numbers with central binomial coefficients. -/
private lemma conv_catalan_centralBinom (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (Nat.centralBinom (n - k) : ℝ)
      = (Nat.centralBinom (n + 1) : ℝ) / 2 := by
  induction n with
  | zero =>
    have h1 : Nat.centralBinom 1 = 2 := by decide
    simp [Nat.centralBinom_zero, catalan_zero, h1]
  | succ n ih =>
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)
        = 4 * ((catalan k : ℝ) * (Nat.centralBinom (n - k) : ℝ))
          - 2 * ((catalan k : ℝ) * (catalan (n - k) : ℝ)) := by
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hcb := cb_succ_real (n - k)
      have hcat := catalan_cast (n - k)
      have hnk : n + 1 - k = (n - k) + 1 := by omega
      have hne : (((n - k : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      rw [hnk, hcb, hcat]
      field_simp
      ring
    have hsum : ∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)
        = 4 * (∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (Nat.centralBinom (n - k) : ℝ))
          - 2 * (∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (catalan (n - k) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hterm
    have hcat : ∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (catalan (n - k) : ℝ)
        = (catalan (n + 1) : ℝ) := by
      have h := catalan_succ' n
      have h2 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => catalan a * catalan b) n
      have h3 : (∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k)) = catalan (n + 1) :=
        h2.symm.trans h.symm
      have hcast : (∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (catalan (n - k) : ℝ))
          = (catalan (n + 1) : ℝ) := by exact_mod_cast h3
      exact hcast
    have hcb2 := cb_succ_real (n + 1)
    have hcat2 := catalan_cast (n + 1)
    have htop : n + 1 - (n + 1) = 0 := by omega
    rw [Finset.sum_range_succ, hsum, ih, hcat, htop,
      Nat.centralBinom_zero, Nat.cast_one, mul_one, hcb2, hcat2]
    have h1 : (((n + 1 : ℕ)) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Reflection symmetry of the Catalan-centralBinom convolution. -/
private lemma conv_reflect (n : ℕ) :
    ∑ i ∈ Finset.range n, (catalan (i + 1) : ℝ) * (Nat.centralBinom (n - i) : ℝ)
      = ∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - i) : ℝ) := by
  rw [← Finset.sum_range_reflect
    (fun i => (catalan (i + 1) : ℝ) * (Nat.centralBinom (n - i) : ℝ)) n]
  apply Finset.sum_congr rfl
  intro i hi
  have hi2 : i < n := Finset.mem_range.mp hi
  have e1 : n - 1 - i + 1 = n - i := by omega
  have e2 : n - (n - 1 - i) = i + 1 := by omega
  rw [e1, e2, mul_comm]

/-- Partial convolution with the top and bottom terms removed. -/
private lemma conv_cb_catalan_part (n : ℕ) :
    ∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - (i + 1) + 1) : ℝ)
      = (Nat.centralBinom (n + 1 + 1) : ℝ) / 2 - (Nat.centralBinom (n + 1) : ℝ)
        - (catalan (n + 1) : ℝ) := by
  have hI := conv_catalan_centralBinom (n + 1)
  rw [Finset.sum_range_succ', Finset.sum_range_succ] at hI
  have e0 : n + 1 - 0 = n + 1 := by omega
  have es : n + 1 - (n + 1) = 0 := by omega
  rw [e0, es, Nat.centralBinom_zero, catalan_zero] at hI
  simp only [Nat.cast_one, mul_one, one_mul] at hI
  have hmid : (∑ i ∈ Finset.range n,
      (catalan (i + 1) : ℝ) * (Nat.centralBinom (n + 1 - (i + 1)) : ℝ))
      = ∑ i ∈ Finset.range n, (catalan (i + 1) : ℝ) * (Nat.centralBinom (n - i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi2 : i < n := Finset.mem_range.mp hi
    have e : n + 1 - (i + 1) = n - i := by omega
    rw [e]
  rw [hmid, conv_reflect] at hI
  have hB : (∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - i) : ℝ))
      = ∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - (i + 1) + 1) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi2 : i < n := Finset.mem_range.mp hi
    have e : n - (i + 1) + 1 = n - i := by omega
    rw [e]
  rw [hB] at hI
  linarith [hI]

/-- Harmonic convolution identity: the coefficient identity behind the log-squared series. -/
private lemma conv_cb_harmonic (n : ℕ) :
    ∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
        / (2 * ((m : ℝ) + 1))
      = (Nat.centralBinom (n + 1) : ℝ)
        * ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcb1 : Nat.centralBinom 1 = 2 := by decide
    -- top term of the peeled sum
    have htop : (Nat.centralBinom (n + 1) : ℝ) * (Nat.centralBinom (n + 1 - (n + 1) + 1) : ℝ)
          / (2 * ((n : ℝ) + 1))
        = (Nat.centralBinom (n + 1) : ℝ) / ((n : ℝ) + 1) := by
      have etop : n + 1 - (n + 1) + 1 = 1 := by omega
      rw [etop, hcb1]
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    -- per-term recurrence for the remaining sum
    have hterm : ∀ m ∈ Finset.range n,
        (Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n + 1 - (m + 1) + 1) : ℝ)
          / (2 * ((m : ℝ) + 1))
        = 4 * ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (2 * ((m : ℝ) + 1)))
          - (Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1)) := by
      intro m hm
      have hm2 : m < n := Finset.mem_range.mp hm
      have e : n + 1 - (m + 1) + 1 = (n - (m + 1) + 1) + 1 := by omega
      have hcb := cb_succ_real (n - (m + 1) + 1)
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hj1 : ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by positivity
      rw [e, hcb]
      field_simp
      ring
    have hrest : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n + 1 - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1)))
        = 4 * (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1)))
          - (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hterm
    -- partial fractions for the error sum
    have hEper : ∀ m ∈ Finset.range n,
        ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
        = (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
          + (Nat.centralBinom (m + 1) : ℝ) * (catalan (n - (m + 1) + 1) : ℝ) := by
      intro m hm
      have hm2 : m < n := Finset.mem_range.mp hm
      have e : m + (n - (m + 1) + 1) + 2 = n + 2 := by omega
      have he : (m : ℝ) + ((((n - (m + 1) + 1 : ℕ)) : ℝ)) + 2 = (n : ℝ) + 2 := by
        exact_mod_cast e
      have hcat := catalan_cast (n - (m + 1) + 1)
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hj1 : ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by positivity
      have hform : ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
              / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
            - ((Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
              * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            + (Nat.centralBinom (m + 1) : ℝ) * (catalan (n - (m + 1) + 1) : ℝ))
          = ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
            * ((((n : ℝ) + 2) - ((m : ℝ) + 1) - ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))
              / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) := by
        rw [hcat]
        field_simp
        ring
      have hside : ((n : ℝ) + 2) - ((m : ℝ) + 1) - ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1) = 0 := by
        linarith [he]
      have h0 : ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
              / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
            - ((Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
              * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            + (Nat.centralBinom (m + 1) : ℝ) * (catalan (n - (m + 1) + 1) : ℝ)) = 0 := by
        rw [hform, hside, zero_div, mul_zero]
      exact eq_of_sub_eq_zero h0
    have hEmul : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
        = (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
          + (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (catalan (n - (m + 1) + 1) : ℝ)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hEper
    have hE' : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1)))
        = ((∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
          + (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (catalan (n - (m + 1) + 1) : ℝ))) / ((n : ℝ) + 2) := by
      have hN : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [eq_div_iff hN]
      exact hEmul
    have hA : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
        = 2 * (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by
        have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        have hm2 : (2 : ℝ) * ((m : ℝ) + 1) ≠ 0 := by positivity
        field_simp)
    have hBval := conv_cb_catalan_part n
    -- harmonic number recurrence
    have hΔ : (∑ k ∈ Finset.range (2 * (n + 1 + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1 + 1), ((k : ℝ) + 1)⁻¹)
        = ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹))
          + (2 * (n : ℝ) + 2)⁻¹ + (2 * (n : ℝ) + 3)⁻¹ - ((n : ℝ) + 2)⁻¹ := by
      have eH1 : 2 * (n + 1 + 1) - 1 = 2 * (n + 1) - 1 + 1 + 1 := by omega
      rw [eH1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have f1 : ((((2 * (n + 1) - 1 + 1 : ℕ)) : ℝ) + 1)⁻¹ = (2 * (n : ℝ) + 3)⁻¹ := by
        have e : (2 * (n + 1) - 1 + 1 : ℕ) = 2 * n + 1 + 1 := by omega
        rw [e]
        have en : ((((2 * n + 1 + 1 : ℕ)) : ℝ) + 1) = 2 * (n : ℝ) + 3 := by push_cast; ring
        rw [en]
      have f2 : ((((2 * (n + 1) - 1 : ℕ)) : ℝ) + 1)⁻¹ = (2 * (n : ℝ) + 2)⁻¹ := by
        have e : (2 * (n + 1) - 1 : ℕ) = 2 * n + 1 := by omega
        rw [e]
        have en : ((((2 * n + 1 : ℕ)) : ℝ) + 1) = 2 * (n : ℝ) + 2 := by push_cast; ring
        rw [en]
      have g1 : ((((n + 1 : ℕ)) : ℝ) + 1)⁻¹ = ((n : ℝ) + 2)⁻¹ := by
        have en : ((((n + 1 : ℕ)) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
        rw [en]
      rw [f1, f2, g1]
      ring
    have hcb2 := cb_succ_real (n + 1)
    have hcat2 := catalan_cast (n + 1)
    conv_lhs => rw [Finset.sum_range_succ]
    rw [hrest, hE', hA, ih, hBval, htop, hΔ, hcb2, hcat2]
    push_cast
    have g1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have g2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have g2' : (((n : ℝ) + 1) + 1) ≠ 0 := by positivity
    have g3 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    have g4 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    have g5 : ((((n + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by positivity
    have g0 : ((((n + 1 : ℕ)) : ℝ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring

/-- Coefficient identity for the derivative of the log series. -/
private lemma conv_for_deriv (n : ℕ) :
    ((n : ℝ) + 1) * (catalan (n + 1) : ℝ)
      = ∑ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2) := by
  have hI := conv_catalan_centralBinom (n + 1)
  rw [Finset.sum_range_succ] at hI
  have etop : n + 1 - (n + 1) = 0 := by omega
  rw [etop, Nat.centralBinom_zero, Nat.cast_one, mul_one] at hI
  have h1 : (∑ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2))
      = (∑ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)) / 2 := by
    have h1a : (∑ k ∈ Finset.range (n + 1),
          (catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2))
        = ∑ k ∈ Finset.range (n + 1),
          (((catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)) / 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      have e : n - k + 1 = n + 1 - k := by omega
      rw [e]
      ring
    rw [h1a, Finset.sum_div]
  have hcb2 := cb_succ_real (n + 1)
  have hcat2 := catalan_cast (n + 1)
  rw [h1]
  rw [hcb2] at hI
  rw [hcat2] at hI ⊢
  have hD : ((((n + 1 : ℕ))) : ℝ) + 1 ≠ 0 := by positivity
  push_cast at hI ⊢
  field_simp at hI ⊢
  linarith

/-- Coefficient identity for squaring the log series. -/
private lemma conv_for_square (n : ℕ) :
    2 * (∑ k ∈ Finset.range (n + 1),
      ((Nat.centralBinom k : ℝ) / (2 * (k : ℝ)) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)))
      = (Nat.centralBinom (n + 1) : ℝ)
        * ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) := by
  have hC := conv_cb_harmonic n
  have hsplit : (∑ k ∈ Finset.range (n + 1),
        ((Nat.centralBinom k : ℝ) / (2 * (k : ℝ)) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)))
      = ∑ j ∈ Finset.range n,
        ((Nat.centralBinom (j + 1) : ℝ) / (2 * ((j : ℝ) + 1))
          * ((Nat.centralBinom (n - (j + 1) + 1) : ℝ) / 2)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.centralBinom_zero, Nat.cast_one, Nat.cast_zero, mul_zero, div_zero,
      zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Nat.cast_add, Nat.cast_one]
  have h23 : 2 * (∑ j ∈ Finset.range n,
        ((Nat.centralBinom (j + 1) : ℝ) / (2 * ((j : ℝ) + 1))
          * ((Nat.centralBinom (n - (j + 1) + 1) : ℝ) / 2)))
      = ∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
        * (Nat.centralBinom (n - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hsplit, h23]
  exact hC

/-- Summable geometric majorant for power-series derivative bounds. -/
private lemma majorant_summable (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 ≤ R) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5) := by
  have h4 : (4 : ℝ) * R < 1 := by linarith [hR4]
  have hnn : (0 : ℝ) ≤ 4 * R := by positivity
  have h4R : ‖(4 : ℝ) * R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact h4
  have hW : Summable (fun n : ℕ => ((n : ℝ) + 1) * ((4 : ℝ) * R) ^ n) := by
    have hgeom := (hasSum_choose_mul_geometric_of_norm_lt_one 1 h4R).summable
    have heq : (fun n : ℕ => ((n : ℝ) + 1) * ((4 : ℝ) * R) ^ n)
        = (fun n : ℕ => (((n + 1).choose 1 : ℕ) : ℝ) * ((4 : ℝ) * R) ^ n) := by
      funext n
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact hgeom
  have e : (fun n : ℕ => ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5)
      = (fun n : ℕ => (((n : ℝ) + 1) * ((4 : ℝ) * R) ^ n) * 20) := by
    funext n
    ring
  rw [e]
  exact hW.mul_right 20

/-- Termwise derivative of the Catalan generating function on a ball. -/
private lemma S_hasDerivAt (x : ℝ) (_hx : |x| < 1 / 4) (R : ℝ) (_hR1 : |x| < R)
    (hR4 : R < 1 / 4) (hR8 : 1 / 8 ≤ R) (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt (fun t => ∑' n, (catalan n : ℝ) * t ^ n)
      (∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n) y := by
  have hR0 : 0 < R := by linarith [hR8]
  have hU : Summable (fun n : ℕ => ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5) :=
    majorant_summable R hR4 (le_of_lt hR0)
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hS0 : Summable (fun n => (catalan n : ℝ) * (0 : ℝ) ^ n) :=
    summable_cat 0 (by norm_num)
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.ball (0 : ℝ) R,
      ‖(catalan n : ℝ) * ((n : ℝ) * t ^ (n - 1))‖
        ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
    intro n t ht
    have e0 : (catalan n : ℝ) * ((n : ℝ) * t ^ (n - 1))
        = (catalan n : ℝ) * (n : ℝ) * t ^ (n - 1) := by ring
    rw [e0]
    have htb : |t| ≤ R := le_of_lt (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h)
    have hC : (catalan n : ℝ) ≤ 4 ^ n := cat_le_four_pow n
    have hnn : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
    by_cases hn : n = 0
    · subst hn
      simp only [catalan_zero, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, norm_zero,
        pow_zero]
      positivity
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hpow : |t| ^ (n - 1) ≤ R ^ (n - 1) :=
        pow_le_pow_left₀ (abs_nonneg t) htb (n - 1)
      have hN : (n : ℝ) ≤ ((n : ℝ) + 1) * (20 * R) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n, hR8,
          mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (by linarith [hR8] : (0 : ℝ) ≤ 20 * R - 1),
          hR0.le]
      have hnorm : ‖(catalan n : ℝ) * (n : ℝ) * t ^ (n - 1)‖
          = (catalan n : ℝ) * (n : ℝ) * |t| ^ (n - 1) := by
        simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
      have step1 : (catalan n : ℝ) * (n : ℝ) * |t| ^ (n - 1)
          ≤ (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1) := by
        have e1 : (catalan n : ℝ) * (n : ℝ) * |t| ^ (n - 1)
            = ((catalan n : ℝ) * |t| ^ (n - 1)) * (n : ℝ) := by ring
        have e2 : (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1)
            = ((4 : ℝ) ^ n * R ^ (n - 1)) * (n : ℝ) := by ring
        rw [e1, e2]
        apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
        apply mul_le_mul hC hpow (pow_nonneg (abs_nonneg t) _)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
      have step2 : (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1)
          ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
        have eR : R ^ (n - 1) * R = R ^ n := by
          have e1 : n - 1 + 1 = n := by omega
          rw [← pow_succ, e1]
        have h1 : (n : ℝ) * ((4 : ℝ) ^ n * R ^ (n - 1))
            ≤ (((n : ℝ) + 1) * (20 * R)) * ((4 : ℝ) ^ n * R ^ (n - 1)) :=
          mul_le_mul_of_nonneg_right hN
            (mul_nonneg (pow_nonneg (by norm_num) n) (pow_nonneg hR0.le _))
        have h2 : (((n : ℝ) + 1) * (20 * R)) * ((4 : ℝ) ^ n * R ^ (n - 1))
            = ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
          calc (((n : ℝ) + 1) * (20 * R)) * ((4 : ℝ) ^ n * R ^ (n - 1))
              = ((n : ℝ) + 1) * (4 : ℝ) ^ n * (R ^ (n - 1) * R) * 20 := by ring
            _ = ((n : ℝ) + 1) * (4 : ℝ) ^ n * (R ^ n) * 20 := by rw [eR]
            _ = ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by ring
        have e3 : (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1)
            = (n : ℝ) * ((4 : ℝ) ^ n * R ^ (n - 1)) := by ring
        rw [e3]
        linarith [h1, h2]
      rw [hnorm]
      linarith [step1, step2]
  have hmain : HasDerivAt (fun z => ∑' n, (catalan n : ℝ) * z ^ n)
      (∑' n, (catalan n : ℝ) * ((n : ℝ) * y ^ (n - 1))) y :=
    hasDerivAt_tsum_of_isPreconnected hU hopen hconn
      (fun n t _ => ((hasDerivAt_pow n t).const_mul (catalan n : ℝ)))
      (fun n t ht => hbound n t ht) hy0 hS0 hy
  have hshift : (∑' n, (catalan n : ℝ) * ((n : ℝ) * y ^ (n - 1)))
      = ∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n := by
    have hFsumm : Summable (fun n => (catalan n : ℝ) * ((n : ℝ) * y ^ (n - 1))) := by
      apply Summable.of_norm
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hU
      intro n
      exact hbound n y hy
    rw [hFsumm.tsum_eq_zero_add]
    simp only [catalan_zero, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul, zero_add]
    apply tsum_congr
    intro n
    have e : n + 1 - 1 = n := by omega
    have ecast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, ecast]
    ring
  rw [hshift] at hmain
  exact hmain

private lemma cb_le_four_pow_real (n : ℕ) : (Nat.centralBinom n : ℝ) ≤ (4 : ℝ) ^ n := by
  exact_mod_cast Nat.centralBinom_le_four_pow n

private lemma summable_cbnorm (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => ‖(Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n‖) := by
  have hq : (4 : ℝ) * |y| < 1 := by linarith [hy]
  have hnn : (0 : ℝ) ≤ 4 * |y| := by positivity
  have hgeom := summable_geometric_of_lt_one hnn hq
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ (hgeom.mul_left 2)
  intro n
  have hC : (Nat.centralBinom (n + 1) : ℝ) ≤ 4 ^ (n + 1) := cb_le_four_pow_real _
  have hnn2 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn2]
  calc (Nat.centralBinom (n + 1) : ℝ) / 2 * |y| ^ n
      ≤ (4 ^ (n + 1) / 2) * |y| ^ n :=
        mul_le_mul_of_nonneg_right (by linarith [hC]) (pow_nonneg (abs_nonneg y) n)
    _ = 2 * (4 * |y|) ^ n := by ring

private lemma summable_cb (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) :=
  (summable_cbnorm y hy).of_norm

private lemma majorant_cb_summable (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 ≤ R) :
    Summable (fun n : ℕ => 2 * ((4 : ℝ) * R) ^ n) := by
  have h4 : (4 : ℝ) * R < 1 := by linarith [hR4]
  have hnn : (0 : ℝ) ≤ 4 * R := by positivity
  exact (summable_geometric_of_lt_one hnn h4).mul_left 2

/-- Termwise derivative of the integrated b-series on a ball. -/
private lemma H_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt
      (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
      (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) y := by
  have hU := majorant_cb_summable R hR4 hR0.le
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hzero : (fun n => ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1))
      = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  have hS0 : Summable
      (fun n => ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) := by
    rw [hzero]
    exact summable_zero
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.ball (0 : ℝ) R,
      ‖((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)‖
        ≤ 2 * ((4 : ℝ) * R) ^ n := by
    intro n t ht
    have htb : |t| ≤ R := le_of_lt (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h)
    have hC : (Nat.centralBinom (n + 1) : ℝ) ≤ 4 ^ (n + 1) := cb_le_four_pow_real _
    have hnn2 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by positivity
    have hcancel : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)
        = ((Nat.centralBinom (n + 1) : ℝ) / 2) * t ^ n := by
      have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hcancel, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn2]
    have hpow : |t| ^ n ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg t) htb n
    calc (Nat.centralBinom (n + 1) : ℝ) / 2 * |t| ^ n
        ≤ (4 ^ (n + 1) / 2) * R ^ n := by
          apply mul_le_mul _ hpow (pow_nonneg (abs_nonneg t) _) (by positivity)
          linarith [hC]
      _ = 2 * ((4 : ℝ) * R) ^ n := by ring
  have hmain : HasDerivAt
      (fun z => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * z ^ (n + 1))
      (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * y ^ n))
      y :=
    hasDerivAt_tsum_of_isPreconnected hU hopen hconn
      (fun n t _ => by
        have h1 := ((hasDerivAt_pow (n + 1) t).const_mul
          ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)))
        have e1 : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have e2 : n + 1 - 1 = n := by omega
        rw [e1, e2] at h1
        have heq : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)
            = ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n) :=
          rfl
        rwa [heq] at h1)
      (fun n t ht => hbound n t ht) hy0 hS0 hy
  have hcongr : (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1))
        * (((n : ℝ) + 1) * y ^ n))
      = ∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n := by
    apply tsum_congr
    intro n
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hcongr] at hmain
  exact hmain

/-- Cauchy product: the Catalan series times the b-series is the derivative series. -/
private lemma S_mul_B (y : ℝ) (hy : |y| < 1 / 4) :
    (∑' n, (catalan n : ℝ) * y ^ n) * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
      = ∑' n : ℕ, (((n : ℝ) + 1) * (catalan (n + 1) : ℝ)) * y ^ n := by
  have hSn := summable_cat_norm y hy
  have hBn := summable_cbnorm y hy
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hSn hBn]
  apply tsum_congr
  intro n
  have hcf := conv_for_deriv n
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((catalan k : ℝ) * y ^ k) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2 * y ^ (n - k))
        = ((catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)) * y ^ n := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hpow : y ^ k * y ^ (n - k) = y ^ n := by
      rw [← pow_add]
      congr 1
      omega
    calc ((catalan k : ℝ) * y ^ k) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2 * y ^ (n - k))
        = ((catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)) * (y ^ k * y ^ (n - k)) := by
          ring
      _ = ((catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)) * y ^ n := by
          rw [hpow]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hcf]

/-- Derivative of the log-Catalan series is the b-series. -/
private lemma L_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (_hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
      (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) y := by
  have hmem : |y| < R := by
    have h := Metric.mem_ball.mp hy
    rwa [dist_zero_right, Real.norm_eq_abs] at h
  have hy4 : |y| < 1 / 4 := lt_trans hmem hR4
  have hS := S_hasDerivAt y hy4 R hmem hR4 hR8 y hy
  have hB := S_mul_B y hy4
  have hSne : (∑' n, (catalan n : ℝ) * y ^ n) ≠ 0 := ne_of_gt (catalan_tsum_pos y hy4)
  have hlog := hS.log hSne
  have hder : (∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n)
          / (∑' n, (catalan n : ℝ) * y ^ n)
      = ∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n := by
    have hS' : (∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n)
        = (∑' n, (catalan n : ℝ) * y ^ n) * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) := by
      rw [hB]
      apply tsum_congr
      intro n
      ring
    rw [hS', div_eq_iff hSne]
    exact mul_comm _ _
  rwa [hder] at hlog

private lemma S_tsum_zero : (∑' n, (catalan n : ℝ) * (0 : ℝ) ^ n) = 1 := by
  have hS := summable_cat 0 (by norm_num)
  rw [hS.tsum_eq_zero_add]
  have htail : (∑' n, (catalan (n + 1) : ℝ) * (0 : ℝ) ^ (n + 1)) = 0 := by
    have hzero : (fun n => (catalan (n + 1) : ℝ) * (0 : ℝ) ^ (n + 1)) = fun _ => 0 := by
      funext n
      simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
    rw [hzero]
    exact tsum_zero
  rw [htail]
  simp [catalan_zero]

private lemma H_tsum_zero :
    (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1))
    = 0 := by
  have hzero : (fun n => ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1))
      = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [hzero]
  exact tsum_zero

/-- The log-Catalan series equals the integrated b-series on the ball. -/
private lemma L_eq_H (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    Real.log (∑' n, (catalan n : ℝ) * y ^ n)
      = ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1) := by
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hL : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n) t :=
    fun t ht => L_hasDerivAt R hR4 hR0 hR8 t ht
  have hH : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt
        (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
        (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n) t :=
    fun t ht => H_hasDerivAt R hR4 hR0 t ht
  have hdL : DifferentiableOn ℝ (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hL t ht).differentiableAt).differentiableWithinAt
  have hdH : DifferentiableOn ℝ
      (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hH t ht).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn
      (deriv (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n)))
      (deriv (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1)))
      (Metric.ball (0 : ℝ) R) := by
    intro t ht
    rw [(hL t ht).deriv, (hH t ht).deriv]
  have h0 : Real.log (∑' n, (catalan n : ℝ) * (0 : ℝ) ^ n)
      = ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1) := by
    rw [S_tsum_zero, H_tsum_zero, Real.log_one]
  have heq := IsOpen.eqOn_of_deriv_eq hopen hconn hdL hdH hderiv hy0 h0
  exact heq hy

/-- Harmonic-number difference driving the log-squared coefficients. -/
private noncomputable def harmDiff (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
    - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)

/-- Unnormalized log-squared coefficient. -/
private noncomputable def harmD (n : ℕ) : ℝ := (Nat.centralBinom (n + 1) : ℝ) * harmDiff n

private lemma harmDiff_nonneg (n : ℕ) : 0 ≤ harmDiff n := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (2 * (n + 1) - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have h : (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)
      ≤ (∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
  simp only [harmDiff]
  linarith [h]

private lemma harmDiff_le (n : ℕ) : harmDiff n ≤ (n : ℝ) := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (2 * (n + 1) - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have hinter : Finset.range (n + 1) ∩ Finset.range (2 * (n + 1) - 1)
      = Finset.range (n + 1) := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_range]
    omega
  have hcard : (Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1)).card = n := by
    rw [Finset.card_sdiff, hinter, Finset.card_range, Finset.card_range]
    omega
  have hsplit : harmDiff n
      = ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹ := by
    simp only [harmDiff]
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  rw [hsplit]
  calc ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹
      ≤ ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), 1 :=
        Finset.sum_le_sum (fun k _ => inv_le_one_of_one_le₀ (by
          have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
          linarith [hk]))
    _ = ((Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (n : ℝ) := by rw [hcard]

private lemma harmD_zero : harmD 0 = 0 := by
  have e1 : 2 * (0 + 1) - 1 = 1 := by norm_num
  have e2 : 0 + 1 = 1 := by norm_num
  simp only [harmD, harmDiff]
  rw [e1, e2, sub_self, mul_zero]

private lemma summable_dnorm (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => ‖harmD n * y ^ n‖) := by
  have hM := majorant_summable |y| hy (abs_nonneg y)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hM
  intro n
  have hcb : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) := by positivity
  have hΔ := harmDiff_nonneg n
  have hΔle := harmDiff_le n
  have hC := cb_le_four_pow_real (n + 1)
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hDnn : 0 ≤ harmD n := by
    simp only [harmD]
    exact mul_nonneg hcb hΔ
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hDnn]
  have s1 : harmD n ≤ 4 ^ (n + 1) * (n : ℝ) := by
    simp only [harmD]
    exact mul_le_mul hC hΔle hΔ (by positivity)
  have step1 : harmD n * |y| ^ n ≤ (4 ^ (n + 1) * (n : ℝ)) * |y| ^ n :=
    mul_le_mul_of_nonneg_right s1 (pow_nonneg (abs_nonneg y) n)
  have step2 : (4 ^ (n + 1) * (n : ℝ)) * |y| ^ n
      ≤ ((n : ℝ) + 1) * 4 ^ (n + 1) * |y| ^ n * 5 := by
    have e : ((n : ℝ) + 1) * 4 ^ (n + 1) * |y| ^ n * 5 - (4 ^ (n + 1) * (n : ℝ)) * |y| ^ n
        = (4 ^ (n + 1) * |y| ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by ring
    have hpos : (0 : ℝ) ≤ (4 ^ (n + 1) * |y| ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (pow_nonneg (abs_nonneg y) n)
      · linarith [hnn]
    linarith [hpos]
  linarith [step1, step2]

private lemma summable_Hnorm (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => ‖((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1)‖) := by
  have hB := summable_cbnorm y hy
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ (hB.mul_left |y|)
  intro n
  have hnn2 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1) := by positivity
  have hnn3 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by positivity
  have h1 : ‖((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1)‖
      = ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ (n + 1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn2]
  rw [h1]
  have hle : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1))
      ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by
    apply div_le_self (by positivity)
    have h1le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith [hnn]
    exact h1le
  have e : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ (n + 1)
      = |y| * (((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ n) := by ring
  have h2 : (Nat.centralBinom (n + 1) : ℝ) / 2 * |y| ^ n
      = ‖(Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn3]
  have h3 : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ n
      ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 * |y| ^ n :=
    mul_le_mul_of_nonneg_right hle (pow_nonneg (abs_nonneg y) n)
  rw [e, ← h2]
  exact mul_le_mul_of_nonneg_left h3 (abs_nonneg y)

/-- Shifted coefficient identity: twice the H-B convolution coefficient
    is the next d-coefficient. -/
private lemma hper_sum (N : ℕ) :
    2 * (∑ k ∈ Finset.range (N + 1),
      (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
        * ((Nat.centralBinom (N - k + 1) : ℝ) / 2)))
      = harmD (N + 1) := by
  have hC := conv_for_square (N + 1)
  have hbridge : (∑ k ∈ Finset.range (N + 1),
        (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2)))
      = ∑ k ∈ Finset.range (N + 1 + 1),
        ((Nat.centralBinom k : ℝ) / (2 * (k : ℝ))
          * ((Nat.centralBinom (N + 1 - k + 1) : ℝ) / 2)) := by
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.centralBinom_zero, Nat.cast_zero, mul_zero, div_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have e : N + 1 - (k + 1) + 1 = N - k + 1 := by
      have hkn : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      omega
    rw [e]
    push_cast
    rw [div_div]
  rw [hbridge]
  simp only [harmD, harmDiff]
  exact hC

/-- Termwise derivative of the integrated d-series on a ball. -/
private lemma K_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt
      (fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      (∑' n, harmD n * y ^ n) y := by
  have hU := majorant_summable R hR4 hR0.le
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hzero : (fun n => (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  have hS0 : Summable (fun n => (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) := by
    rw [hzero]
    exact summable_zero
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.ball (0 : ℝ) R,
      ‖(harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)‖
        ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
    intro n t ht
    have htb : |t| ≤ R := le_of_lt (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h)
    have hDnn : 0 ≤ harmD n := by
      simp only [harmD]
      exact mul_nonneg (by positivity) (harmDiff_nonneg n)
    have hcancel : (harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)
        = harmD n * t ^ n := by
      have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hcancel, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hDnn]
    have hpow : |t| ^ n ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg t) htb n
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have s1 : harmD n ≤ 4 ^ (n + 1) * (n : ℝ) := by
      simp only [harmD]
      exact mul_le_mul (cb_le_four_pow_real _) (harmDiff_le n) (harmDiff_nonneg n) (by positivity)
    have step1 : harmD n * |t| ^ n ≤ (4 ^ (n + 1) * (n : ℝ)) * R ^ n :=
      mul_le_mul s1 hpow (pow_nonneg (abs_nonneg t) _) (by positivity)
    have step2 : (4 ^ (n + 1) * (n : ℝ)) * R ^ n
        ≤ ((n : ℝ) + 1) * 4 ^ (n + 1) * R ^ n * 5 := by
      have e : ((n : ℝ) + 1) * 4 ^ (n + 1) * R ^ n * 5 - (4 ^ (n + 1) * (n : ℝ)) * R ^ n
          = (4 ^ (n + 1) * R ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by ring
      have hpos : (0 : ℝ) ≤ (4 ^ (n + 1) * R ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by
        apply mul_nonneg
        · exact mul_nonneg (by positivity) (pow_nonneg hR0.le n)
        · linarith [hnn]
      linarith [hpos]
    linarith [step1, step2]
  have hmain : HasDerivAt
      (fun z => ∑' n, (harmD n / ((n : ℝ) + 1)) * z ^ (n + 1))
      (∑' n, (harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * y ^ n))
      y :=
    hasDerivAt_tsum_of_isPreconnected hU hopen hconn
      (fun n t _ => by
        have h1 := ((hasDerivAt_pow (n + 1) t).const_mul (harmD n / ((n : ℝ) + 1)))
        have e1 : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have e2 : n + 1 - 1 = n := by omega
        rw [e1, e2] at h1
        exact h1)
      (fun n t ht => hbound n t ht) hy0 hS0 hy
  have hcongr : (∑' n, (harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * y ^ n))
      = ∑' n, harmD n * y ^ n := by
    apply tsum_congr
    intro n
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hcongr] at hmain
  exact hmain

/-- Cauchy product: the H-series times the b-series is the half-d-series. -/
private lemma H_mul_B (y : ℝ) (hy : |y| < 1 / 4) :
    (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1))
      * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
    = ∑' N, (harmD (N + 1) / 2) * y ^ (N + 1) := by
  have hHn := summable_Hnorm y hy
  have hBn := summable_cbnorm y hy
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hHn hBn]
  apply tsum_congr
  intro N
  have hpow : ∀ k ∈ Finset.range (N + 1), y ^ (k + 1) * y ^ (N - k) = y ^ (N + 1) := by
    intro k hk
    have hkn : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [← pow_add]
    congr 1
    omega
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1)) * y ^ (k + 1))
        * (((Nat.centralBinom (N - k + 1) : ℝ) / 2) * y ^ (N - k))
      = ((((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2))) * y ^ (N + 1) := by
    intro k hk
    calc (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1)) * y ^ (k + 1))
            * (((Nat.centralBinom (N - k + 1) : ℝ) / 2) * y ^ (N - k))
        = ((((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
            * ((Nat.centralBinom (N - k + 1) : ℝ) / 2))) * (y ^ (k + 1) * y ^ (N - k)) := by
          ring
      _ = ((((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2))) * y ^ (N + 1) := by
          rw [hpow k hk]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hS : (∑ k ∈ Finset.range (N + 1),
        (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2)))
      = harmD (N + 1) / 2 := by
    have hper := hper_sum N
    linarith [hper]
  rw [hS]

/-- Derivative of the squared log-Catalan series. -/
private lemma M_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt (fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n)) ^ 2)
      (2 * (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)) y := by
  have hL := L_hasDerivAt R hR4 hR0 hR8 y hy
  have h2 := hL.mul hL
  have heq : (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
          * (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
        + (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
          * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
      = 2 * (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) := by ring
  rw [heq] at h2
  have hEq : ∀ t, (Real.log (∑' n, (catalan n : ℝ) * t ^ n)) ^ 2
      = ((fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))) t := by
    intro t
    rw [Pi.mul_apply, pow_two]
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hEq)

private lemma K_tsum_zero : (∑' n, (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) = 0 := by
  have hzero : (fun n => (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [hzero]
  exact tsum_zero

/-- The squared log-Catalan series equals the integrated d-series on the ball. -/
private lemma M_eq_K (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    (Real.log (∑' n, (catalan n : ℝ) * y ^ n)) ^ 2
      = ∑' n, (harmD n / ((n : ℝ) + 1)) * y ^ (n + 1) := by
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hLH : ∀ t ∈ Metric.ball (0 : ℝ) R,
      Real.log (∑' n, (catalan n : ℝ) * t ^ n)
        = ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1) :=
    fun t ht => L_eq_H R hR4 hR0 hR8 t ht
  have hHB : ∀ t ∈ Metric.ball (0 : ℝ) R,
      (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)
      = ∑' N, (harmD (N + 1) / 2) * t ^ (N + 1) := by
    intro t ht
    have ht4 : |t| < 1 / 4 := lt_trans (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h) hR4
    exact H_mul_B t ht4
  have hMD : ∀ t ∈ Metric.ball (0 : ℝ) R,
      2 * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)
      = ∑' n, harmD n * t ^ n := by
    intro t ht
    have ht4 : |t| < 1 / 4 := lt_trans (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h) hR4
    have hDsumm : Summable (fun n => harmD n * t ^ n) := (summable_dnorm t ht4).of_norm
    have hDshift : (∑' n, harmD n * t ^ n) = ∑' n, harmD (n + 1) * t ^ (n + 1) := by
      rw [hDsumm.tsum_eq_zero_add]
      have hd0 : harmD 0 * t ^ 0 = 0 := by rw [harmD_zero, zero_mul]
      simp only [hd0, zero_add]
    calc 2 * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
            * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)
        = 2 * ((∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
            * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)) := by
          rw [hLH t ht]; ring
      _ = 2 * (∑' n, (harmD (n + 1) / 2) * t ^ (n + 1)) := by rw [hHB t ht]
      _ = ∑' n, harmD (n + 1) * t ^ (n + 1) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro N
          ring
      _ = ∑' n, harmD n * t ^ n := hDshift.symm
  have hM' : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt (fun s => (Real.log (∑' n, (catalan n : ℝ) * s ^ n)) ^ 2)
        (2 * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
          * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)) t :=
    fun t ht => M_hasDerivAt R hR4 hR0 hR8 t ht
  have hK' : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt
        (fun s => ∑' n, (harmD n / ((n : ℝ) + 1)) * s ^ (n + 1))
        (∑' n, harmD n * t ^ n) t :=
    fun t ht => K_hasDerivAt R hR4 hR0 t ht
  have hdM : DifferentiableOn ℝ (fun s => (Real.log (∑' n, (catalan n : ℝ) * s ^ n)) ^ 2)
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hM' t ht).differentiableAt).differentiableWithinAt
  have hdK : DifferentiableOn ℝ
      (fun s => ∑' n, (harmD n / ((n : ℝ) + 1)) * s ^ (n + 1))
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hK' t ht).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn
      (deriv (fun s => (Real.log (∑' n, (catalan n : ℝ) * s ^ n)) ^ 2))
      (deriv (fun s => ∑' n, (harmD n / ((n : ℝ) + 1)) * s ^ (n + 1)))
      (Metric.ball (0 : ℝ) R) := by
    intro t ht
    rw [(hM' t ht).deriv, (hK' t ht).deriv, hMD t ht]
  have h0 : (Real.log (∑' n, (catalan n : ℝ) * (0 : ℝ) ^ n)) ^ 2
      = ∑' n, (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1) := by
    rw [S_tsum_zero, Real.log_one, K_tsum_zero]
    norm_num
  have heq := IsOpen.eqOn_of_deriv_eq hopen hconn hdM hdK hderiv hy0 h0
  exact heq hy

/-- The identity holds with `HasSum` for `|x| < 1 / 4`. -/
private lemma interior_HasSum (x : ℝ) (hx : |x| < 1 / 4) :
    HasSum
      (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x ^ (n + 1) / ((n : ℝ) + 1))
      ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
  set R : ℝ := max ((|x| + 1 / 4) / 2) (1 / 8) with hRdef
  have hR1 : |x| < R := by
    rw [hRdef]
    exact lt_of_lt_of_le (by linarith [hx]) (le_max_left _ _)
  have hR4 : R < 1 / 4 := by
    rw [hRdef]
    exact max_lt_iff.mpr ⟨by linarith [hx], by norm_num⟩
  have hR8 : 1 / 8 ≤ R := by
    rw [hRdef]
    exact le_max_right _ _
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR8
  have hy : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact hR1
  have hMK := M_eq_K R hR4 hR0 hR8 x hy
  have hKsumm : Summable (fun n => (harmD n / ((n : ℝ) + 1)) * x ^ (n + 1)) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
      ((summable_dnorm x hx).mul_right (1 / 4 : ℝ))
    intro n
    have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith [hnn]
    have e : (harmD n / ((n : ℝ) + 1)) * x ^ (n + 1)
        = (harmD n * x ^ n) * (x / ((n : ℝ) + 1)) := by ring
    rw [e, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hNpos.le]
    calc |x| / ((n : ℝ) + 1) ≤ (1 / 4) / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_right (le_of_lt hx) hNpos.le
      _ ≤ 1 / 4 := div_le_self (by norm_num) hN1
  have hfun : (fun n => (harmD n / ((n : ℝ) + 1)) * x ^ (n + 1))
      = (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext n
    simp only [harmD, harmDiff, Nat.centralBinom_eq_two_mul_choose]
    ring
  rw [← hfun, hMK]
  exact hKsumm.hasSum

/-- Sharp central-binomial bound from the recurrence ratio. -/
private lemma cb_sqrt_bound (n : ℕ) : (Nat.centralBinom n : ℝ) ≤ 4 ^ n / √(3 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ihn =>
    have hcb := cb_succ_real n
    have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hpos1
    have hsq1 : (0 : ℝ) < √(3 * (n : ℝ) + 1) := by
      apply Real.sqrt_pos.mpr
      positivity
    have hsq4 : (0 : ℝ) < √(3 * (n : ℝ) + 4) := by
      apply Real.sqrt_pos.mpr
      positivity
    have hneS1 : √(3 * (n : ℝ) + 1) ≠ 0 := ne_of_gt hsq1
    have hneS4 : √(3 * (n : ℝ) + 4) ≠ 0 := ne_of_gt hsq4
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hsq : (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 4)
        ≤ (2 * ((n : ℝ) + 1)) ^ 2 * (3 * (n : ℝ) + 1) := by
      have e : (2 * ((n : ℝ) + 1)) ^ 2 * (3 * (n : ℝ) + 1)
            - ((2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 4)) = (n : ℝ) := by ring
      linarith [e, hnn]
    have hA : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
    have hB : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
    have h1 : (2 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4)
        ≤ 2 * ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) := by
      have hs := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB] at hs
      exact hs
    have hPnn : (0 : ℝ) ≤ 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) := by positivity
    have hstep : (Nat.centralBinom (n + 1) : ℝ)
        ≤ 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1)) := by
      rw [hcb]
      exact mul_le_mul_of_nonneg_left ihn hPnn
    have hMpos : (0 : ℝ) < ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4) := by
      positivity
    have e : (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1)))
          * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4))
        = 2 * (2 * (n : ℝ) + 1) * 4 ^ n * √(3 * (n : ℝ) + 4) := by
      field_simp
    have e2 : (4 ^ (n + 1) / √(3 * (n : ℝ) + 4))
          * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4))
        = 4 ^ (n + 1) * ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) := by
      field_simp
    have hle : 2 * (2 * (n : ℝ) + 1) * 4 ^ n * √(3 * (n : ℝ) + 4)
        ≤ 4 ^ (n + 1) * ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) := by
      have hmul := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ 2 * 4 ^ n by positivity)
      have eP : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
      rw [eP]
      linarith [hmul]
    have hfin : 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1))
        ≤ 4 ^ (n + 1) / √(3 * (n : ℝ) + 4) := by
      have hprod : (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1)))
            * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4))
          ≤ (4 ^ (n + 1) / √(3 * (n : ℝ) + 4))
            * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4)) := by
        rw [e, e2]
        exact hle
      exact le_of_mul_le_mul_right hprod hMpos
    have eS : (3 * ((((n + 1 : ℕ))) : ℝ) + 1) = 3 * (n : ℝ) + 4 := by push_cast; ring
    rw [eS]
    exact le_trans hstep hfin

/-- Splitting off the square root from a 3/2 power. -/
private lemma rpow_le_mul_sqrt (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    a ^ (3 / 2 : ℝ) ≤ a * √b := by
  have e : a ^ (3 / 2 : ℝ) = a * √a := by
    have e32 : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [e32, Real.rpow_add ha, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [e]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) ha.le

private lemma summable_rpow32 : Summable (fun n : ℕ => ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹)) := by
  have h : Summable (fun n : ℕ => (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹)) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have h2 := (summable_nat_add_iff 1).mpr h
  have heq : (fun n : ℕ => ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹))
      = (fun n : ℕ => (((((n + 1 : ℕ))) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    funext n
    rw [Nat.cast_add, Nat.cast_one]
  rw [heq]
  exact h2

/-- Pointwise Catalan bound against the 3/2 series. -/
private lemma cat_closed_bound (n : ℕ) :
    (catalan n : ℝ) * (1 / 4 : ℝ) ^ n ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  have hC := catalan_cast n
  have hcb := cb_sqrt_bound n
  have hx1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h14 : (1 / 4 : ℝ) ^ n = 1 / (4 : ℝ) ^ n := by rw [div_pow, one_pow]
  have eCat : (catalan n : ℝ) * (1 / 4 : ℝ) ^ n
      = (Nat.centralBinom n : ℝ) / (((n : ℝ) + 1) * 4 ^ n) := by
    rw [hC, h14, div_mul_div_comm, mul_one]
  have hle1 : (Nat.centralBinom n : ℝ) / (((n : ℝ) + 1) * 4 ^ n)
      ≤ (4 ^ n / √(3 * (n : ℝ) + 1)) / (((n : ℝ) + 1) * 4 ^ n) :=
    div_le_div_of_nonneg_right hcb (by positivity)
  have e2 : (4 ^ n / √(3 * (n : ℝ) + 1)) / (((n : ℝ) + 1) * 4 ^ n)
      = (√(3 * (n : ℝ) + 1) * ((n : ℝ) + 1))⁻¹ := by
    have h1 : (4 : ℝ) ^ n ≠ 0 := by positivity
    have h2 : √(3 * (n : ℝ) + 1) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hx1
    field_simp
  have hrpow := rpow_le_mul_sqrt ((n : ℝ) + 1) (3 * (n : ℝ) + 1) hx1 (by linarith [hnn])
  have hposR : (0 : ℝ) < ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx1 _
  have hposS : (0 : ℝ) < √(3 * (n : ℝ) + 1) * ((n : ℝ) + 1) := by positivity
  have hle2 : (√(3 * (n : ℝ) + 1) * ((n : ℝ) + 1))⁻¹ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    rw [inv_le_inv₀ hposS hposR, mul_comm]
    exact hrpow
  rw [eCat]
  exact le_trans hle1 (by rw [e2]; exact hle2)

/-- The harmonic difference is at most one. -/
private lemma harmDiff_le_one (n : ℕ) : harmDiff n ≤ 1 := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (2 * (n + 1) - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have hsplit : harmDiff n
      = ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹ := by
    simp only [harmDiff]
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hcard : (Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1)).card = n := by
    have hinter : Finset.range (n + 1) ∩ Finset.range (2 * (n + 1) - 1)
        = Finset.range (n + 1) := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_range]
      omega
    rw [Finset.card_sdiff, hinter, Finset.card_range, Finset.card_range]
    omega
  have h1 : ∀ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1),
      ((k : ℝ) + 1)⁻¹ ≤ 1 / ((n : ℝ) + 2) := by
    intro k hk
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hk
    have hkn : n + 1 ≤ k := by omega
    have hcast : ((n : ℝ) + 2) ≤ ((k : ℝ) + 1) := by
      have hc : (((n + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkn
      push_cast at hc
      linarith [hc]
    have hpos1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hpos2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [one_div]
    exact (inv_le_inv₀ hpos2 hpos1).mpr hcast
  rw [hsplit]
  calc ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹
      ≤ ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), (1 / ((n : ℝ) + 2)) :=
        Finset.sum_le_sum h1
    _ = (n : ℝ) * (1 / ((n : ℝ) + 2)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
        have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith [hnn]

/-- Pointwise log-squared coefficient bound against the 3/2 series. -/
private lemma Kterm_closed_bound (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    ‖(Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
      harmDiff n * t ^ (n + 1) / ((n : ℝ) + 1)‖
      ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  have hcb := cb_sqrt_bound (n + 1)
  have hΔ := harmDiff_nonneg n
  have hΔ1 := harmDiff_le_one n
  have hcbnn : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) := by positivity
  have hx1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have ht4 : |t| ^ (n + 1) ≤ (1 / 4 : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg t) ht (n + 1)
  have hCnn : (0 : ℝ) ≤ 4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1) := by
    apply div_nonneg (by positivity) (Real.sqrt_nonneg _)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg hcbnn, abs_of_nonneg hΔ, abs_of_nonneg hx1.le]
  have s1 : (Nat.centralBinom (n + 1) : ℝ) * harmDiff n
      ≤ 4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1) := by
    have hmul := mul_le_mul hcb hΔ1 hΔ hCnn
    simpa using hmul
  have s2 : (Nat.centralBinom (n + 1) : ℝ) * harmDiff n * |t| ^ (n + 1)
      ≤ (4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1)) * (1 / 4 : ℝ) ^ (n + 1) :=
    mul_le_mul s1 ht4 (pow_nonneg (abs_nonneg t) _) hCnn
  have eM : ((4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1)) * (1 / 4 : ℝ) ^ (n + 1))
        / ((n : ℝ) + 1)
      = ((((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1))⁻¹) := by
    have h14 : (1 / 4 : ℝ) ^ (n + 1) = 1 / (4 : ℝ) ^ (n + 1) := by rw [div_pow, one_pow]
    rw [h14]
    have h1 : (4 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    have h2 : √(3 * (((n + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hx1
    field_simp
  have hrpow := rpow_le_mul_sqrt ((n : ℝ) + 1) (3 * (((n + 1 : ℕ)) : ℝ) + 1) hx1 (by
    have ecast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [ecast]
    linarith [hnn])
  have hposR : (0 : ℝ) < ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx1 _
  have hposS : (0 : ℝ) < ((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1) := by positivity
  have eR : ((((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1))⁻¹)
      ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    rw [inv_le_inv₀ hposS hposR]
    exact hrpow
  calc (Nat.centralBinom (n + 1) : ℝ) * harmDiff n * |t| ^ (n + 1) / ((n : ℝ) + 1)
      ≤ ((4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1)) * (1 / 4 : ℝ) ^ (n + 1))
        / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_right s2 hx1.le
    _ = ((((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1))⁻¹) := eM
    _ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := eR

private lemma Scat_closed_bound (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    ‖(catalan n : ℝ) * t ^ n‖ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  have hnn : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn]
  have ht4 : |t| ^ n ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ (abs_nonneg t) ht n
  have s1 : (catalan n : ℝ) * |t| ^ n ≤ (catalan n : ℝ) * (1 / 4 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left ht4 hnn
  exact le_trans s1 (cat_closed_bound n)

private lemma summable_cat_closed (t : ℝ) (ht : |t| ≤ 1 / 4) :
    Summable (fun n => ‖(catalan n : ℝ) * t ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ summable_rpow32
  intro n
  exact Scat_closed_bound n t ht

private lemma harmD_target_eq (n : ℕ) (t : ℝ) :
    (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)
      = (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * harmDiff n * t ^ (n + 1) / ((n : ℝ) + 1) := by
  simp only [harmD, Nat.centralBinom_eq_two_mul_choose]
  ring

private lemma summable_Kharm_closed (t : ℝ) (ht : |t| ≤ 1 / 4) :
    Summable (fun n => ‖(harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ summable_rpow32
  intro n
  rw [harmD_target_eq n t]
  exact Kterm_closed_bound n t ht

/-- The Catalan generating function is positive on the closed disc. -/
private lemma S_pos_closed (t : ℝ) (ht : |t| ≤ 1 / 4) :
    0 < ∑' n, (catalan n : ℝ) * t ^ n := by
  have hsum : Summable (fun n => (catalan n : ℝ) * t ^ n) :=
    (summable_cat_closed t ht).of_norm
  have hE : ∀ K, (1 : ℝ) + t ≤ ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * t ^ n := by
    intro K
    induction K with
    | zero =>
      have e0 : 2 * (0 + 1) = 2 := by norm_num
      rw [e0]
      have h2 : ∑ n ∈ Finset.range 2, (catalan n : ℝ) * t ^ n = 1 + t := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp [catalan_zero, catalan_one]
      rw [h2]
    | succ K ih =>
      have hstep : ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * t ^ n
          ≤ ∑ n ∈ Finset.range (2 * (K + 1 + 1)), (catalan n : ℝ) * t ^ n := by
        have e : 2 * (K + 1 + 1) = 2 * (K + 1) + 1 + 1 := by omega
        rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
        have hp := pair_nonneg t ht (K + 1)
        linarith [hp]
      exact le_trans ih hstep
  have hPr : ∀ N, 2 ≤ N → 1 + t ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * t ^ n := by
    intro N hN
    rcases Nat.even_or_odd N with hE' | hO
    · obtain ⟨K, rfl⟩ := hE'
      have hK : 1 ≤ K := by omega
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have h := hE K'
      have e : K' + 1 + (K' + 1) = 2 * (K' + 1) := by omega
      rw [e]
      exact h
    · obtain ⟨K, rfl⟩ := hO
      have hK1 : 1 ≤ K := by omega
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have h1 : ∑ n ∈ Finset.range (2 * (K' + 1)), (catalan n : ℝ) * t ^ n
          ≤ ∑ n ∈ Finset.range (2 * (K' + 1) + 1), (catalan n : ℝ) * t ^ n := by
        rw [Finset.sum_range_succ]
        have hnn : (0 : ℝ) ≤ (catalan (2 * (K' + 1)) : ℝ) * t ^ (2 * (K' + 1)) := by
          apply mul_nonneg (by positivity)
          have e : t ^ (2 * (K' + 1)) = (t ^ (K' + 1)) ^ 2 := by ring
          rw [e]
          exact sq_nonneg _
        linarith [hnn]
      have h2 := hE K'
      linarith [h1, h2]
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (catalan n : ℝ) * t ^ n) Filter.atTop
      (nhds (∑' n, (catalan n : ℝ) * t ^ n)) :=
    (Summable.hasSum_iff_tendsto_nat hsum).mp hsum.hasSum
  have hev : ∀ᶠ N in Filter.atTop, (1 : ℝ) + t ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * t ^ n :=
    Filter.eventually_atTop.mpr ⟨2, fun N hN => hPr N hN⟩
  have hge := ge_of_tendsto hlim hev
  have ht34 : (3 / 4 : ℝ) ≤ 1 + t := by
    have hab : -|t| ≤ t := neg_abs_le t
    linarith [ht, hab]
  linarith [hge, ht34]

private lemma continuousOn_S_closed :
    ContinuousOn (fun t => ∑' n, (catalan n : ℝ) * t ^ n)
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
  have hf : ∀ n : ℕ, ContinuousOn (fun t => (catalan n : ℝ) * t ^ n)
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
    intro n
    exact ((continuous_const.mul (continuous_id.pow n)).continuousOn)
  have hfu : ∀ n : ℕ, ∀ t : ℝ, t ∈ Metric.closedBall 0 (1 / 4 : ℝ) →
      ‖(catalan n : ℝ) * t ^ n‖ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    intro n t ht
    have hmem : |t| ≤ 1 / 4 := by
      have h := Metric.mem_closedBall.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h
    exact Scat_closed_bound n t hmem
  exact continuousOn_tsum hf summable_rpow32 hfu

private lemma continuousOn_Kharm_closed :
    ContinuousOn (fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
  have hf : ∀ n : ℕ, ContinuousOn (fun t => (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
    intro n
    exact ((continuous_const.mul (continuous_id.pow (n + 1))).continuousOn)
  have hfu : ∀ n : ℕ, ∀ t : ℝ, t ∈ Metric.closedBall 0 (1 / 4 : ℝ) →
      ‖(harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)‖ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    intro n t ht
    have hmem : |t| ≤ 1 / 4 := by
      have h := Metric.mem_closedBall.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h
    change ‖(harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)‖ ≤ _
    rw [harmD_target_eq n t]
    exact Kterm_closed_bound n t hmem
  exact continuousOn_tsum hf summable_rpow32 hfu

/-- Interior value identity in product form. -/
private lemma F_eq_G_interior (t : ℝ) (ht : |t| < 1 / 4) :
    (∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      = (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n)) := by
  set R : ℝ := max ((|t| + 1 / 4) / 2) (1 / 8) with hRdef
  have hR1 : |t| < R := by
    rw [hRdef]
    exact lt_of_lt_of_le (by linarith [ht]) (le_max_left _ _)
  have hR4 : R < 1 / 4 := by
    rw [hRdef]
    exact max_lt_iff.mpr ⟨by linarith [ht], by norm_num⟩
  have hR8 : 1 / 8 ≤ R := by
    rw [hRdef]
    exact le_max_right _ _
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR8
  have hy : t ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact hR1
  have hMK := M_eq_K R hR4 hR0 hR8 t hy
  rw [← hMK, pow_two]

/-- The identity holds with `HasSum` on the boundary `|x| = 1 / 4`. -/
private lemma boundary_HasSum (x₀ : ℝ) (hx₀ : |x₀| = 1 / 4) :
    HasSum
      (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1))
      ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x₀ ^ n)) ^ 2) := by
  have hSne : ∀ t ∈ Metric.closedBall (0 : ℝ) (1 / 4 : ℝ),
      (∑' n, (catalan n : ℝ) * t ^ n) ≠ 0 := by
    intro t ht
    have hmem : |t| ≤ 1 / 4 := by
      have h := Metric.mem_closedBall.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h
    exact ne_of_gt (S_pos_closed t hmem)
  have hG_closed : ContinuousOn
      (fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n)))
      (Metric.closedBall 0 (1 / 4 : ℝ)) :=
    (continuousOn_S_closed.log hSne).mul (continuousOn_S_closed.log hSne)
  have hu : ContinuousOn (fun s : ℝ => s * x₀) (Set.Icc 0 1) :=
    (continuous_id.mul_const x₀).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => s * x₀) (Set.Icc 0 1)
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hmem : |(s * x₀)| ≤ 1 / 4 := by
      rw [abs_mul, hx₀, abs_of_nonneg hs.1]
      linarith [hs.2]
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact hmem
  have hFcomp : ContinuousOn
      ((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)) ∘ fun s : ℝ => s * x₀)
      (Set.Icc 0 1) :=
    continuousOn_Kharm_closed.comp hu hmaps
  have hGcomp : ContinuousOn
      ((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀)
      (Set.Icc 0 1) :=
    hG_closed.comp hu hmaps
  have hsn_mem : ∀ n : ℕ, (1 : ℝ) - 1 / ((n : ℝ) + 1) ∈ Set.Icc 0 1 := by
    intro n
    rw [Set.mem_Icc]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith [hnn]
    have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := le_of_lt (by positivity)
    constructor <;> linarith [h0, h1]
  have hsn_lt : ∀ n : ℕ, (1 : ℝ) - 1 / ((n : ℝ) + 1) < 1 := by
    intro n
    have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith [h0]
  have hseq1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hseqIcc : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) - 1 / ((n : ℝ) + 1) ∈ Set.Icc 0 1 :=
    Filter.Eventually.of_forall hsn_mem
  have hseqW :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq1 hseqIcc
  have hmem1 : (1 : ℝ) ∈ Set.Icc 0 1 := Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩
  have hlimF : Filter.Tendsto
      (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
      Filter.atTop
      (nhds (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
        ∘ fun s : ℝ => s * x₀) 1)) :=
    Filter.Tendsto.comp (hFcomp.continuousWithinAt hmem1) hseqW
  have hlimG : Filter.Tendsto
      (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
      Filter.atTop
      (nhds (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀) 1)) :=
    Filter.Tendsto.comp (hGcomp.continuousWithinAt hmem1) hseqW
  have heq_fg : Filter.EventuallyEq Filter.atTop
      (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
      (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) := by
    apply Filter.Eventually.of_forall
    intro n
    simp only [Function.comp_apply]
    have habs : |(1 - 1 / ((n : ℝ) + 1)) * x₀| < 1 / 4 := by
      rw [abs_mul, hx₀]
      have hs0 := (Set.mem_Icc.mp (hsn_mem n)).1
      have hs1 := hsn_lt n
      rw [abs_of_nonneg hs0]
      linarith [hs0, hs1]
    exact F_eq_G_interior _ habs
  have hval : (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      ∘ fun s : ℝ => s * x₀) 1)
      = (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀) 1) :=
    tendsto_nhds_unique_of_eventuallyEq hlimF hlimG heq_fg
  have hvalTS : (∑' n, (harmD n / ((n : ℝ) + 1)) * x₀ ^ (n + 1))
      = (Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n)) := by
    simpa [Function.comp_apply] using hval
  have hKt : Summable (fun n => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
      harmDiff n * x₀ ^ (n + 1) / ((n : ℝ) + 1)) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ summable_rpow32
    intro n
    exact Kterm_closed_bound n x₀ (le_of_eq hx₀)
  have htsum_eq2 : (∑' n, (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1))
      = ∑' n, (harmD n / ((n : ℝ) + 1)) * x₀ ^ (n + 1) := by
    apply tsum_congr
    intro n
    simp only [harmD, harmDiff, Nat.centralBinom_eq_two_mul_choose]
    ring
  have hfun : (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        harmDiff n * x₀ ^ (n + 1) / ((n : ℝ) + 1))
      = (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext n
    simp only [harmDiff]
  have hHas : HasSum
      (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1))
      ((Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n))) := by
    have h1 := hKt.hasSum
    rw [hfun, htsum_eq2, hvalTS] at h1
    exact h1
  rw [pow_two]
  exact hHas

/-- The source-level reciprocal sum is the real cast of `harmonic`. -/
private lemma sum_inv_eq_harmonic_cast (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℝ) + 1)⁻¹) = ((harmonic m : ℚ) : ℝ) := by
  induction m with
  | zero => simp [harmonic_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, harmonic_succ, ih, Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast]
    congr 1
    push_cast
    ring

/-- The canonical summand agrees with the source-level summand. -/
private lemma canonical_term_eq_source (n : ℕ) (x : ℝ) :
    (Nat.centralBinom (n + 1) : ℝ) *
        (((harmonic (2 * (n + 1) - 1) : ℚ) : ℝ) - ((harmonic (n + 1) : ℚ) : ℝ)) *
        x ^ (n + 1) / ((n : ℝ) + 1)
      = (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x ^ (n + 1) / ((n : ℝ) + 1) := by
  rw [Nat.centralBinom_eq_two_mul_choose,
    ← sum_inv_eq_harmonic_cast (2 * (n + 1) - 1),
    ← sum_inv_eq_harmonic_cast (n + 1)]

/--
Knuth's identity for central binomial coefficients and harmonic numbers, stated with the
standard `Nat.centralBinom` and `harmonic` APIs.
This is the canonical form of `knuth_catalan_log_sq` below.
-/
theorem knuth_catalan_log_sq_canonical (x : ℝ) (hx : |x| ≤ 1 / 4) :
  HasSum
    (fun n : ℕ => (Nat.centralBinom (n + 1) : ℝ) *
      (((harmonic (2 * (n + 1) - 1) : ℚ) : ℝ) - ((harmonic (n + 1) : ℚ) : ℝ)) *
      x ^ (n + 1) / ((n : ℝ) + 1))
    ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact (interior_HasSum x hlt).congr_fun (fun n => canonical_term_eq_source n x)
  · exact (boundary_HasSum x heq).congr_fun (fun n => canonical_term_eq_source n x)

/--
Knuth's identity for central binomial coefficients and harmonic numbers.

Source: Hongwei Chen, "Interesting Series Associated with Central Binomial Coefficients, Catalan
Numbers and Harmonic Numbers", Journal of Integer Sequences 19 (2016), Article 16.1.5, Theorem
`eq:k_gf`, lines 229-234, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Chen/chen21.tex>.

Proves `Wanted` entry `knuth_catalan_log_sq`.
-/
theorem knuth_catalan_log_sq (x : ℝ) (hx : |x| ≤ 1 / 4) :
  HasSum
    (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
      ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
        (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
      x ^ (n + 1) / ((n : ℝ) + 1))
    ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
  exact (knuth_catalan_log_sq_canonical x hx).congr_fun
    (fun n => (canonical_term_eq_source n x).symm)

end MetaMathlibExt
end
