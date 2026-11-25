/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Stolz–Cesàro theorem.** Let $(a_n)_{n \ge 0}$ and $(b_n)_{n \ge 0}$ be sequences of
real numbers such that $(b_n)$ is strictly increasing and $b_n \to +\infty$ as $n \to \infty$,
and let $L$ be a real number. If
$\frac{a_{n+1} - a_n}{b_{n+1} - b_n} \to L$ as $n \to \infty$, then
$\frac{a_n}{b_n} \to L$ as $n \to \infty$.

Source: https://en.wikipedia.org/wiki/Stolz%E2%80%93Ces%C3%A0ro_theorem.
Proves `Wanted` entry `stolz_cesaro`.
-/
theorem stolz_cesaro {a b : ℕ → ℝ} {L : ℝ}
    (hb_mono : StrictMono b)
    (hb_unbounded : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hlim : Filter.Tendsto (fun n => (a (n + 1) - a n) / (b (n + 1) - b n))
      Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => a n / b n) Filter.atTop (nhds L) := by
  have hd_pos : ∀ n, 0 < b (n + 1) - b n :=
    fun n => sub_pos.mpr (hb_mono (Nat.lt_succ_self n))
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := hlim (ε / 3) (by linarith)
  set C := a N1 - L * b N1 with hC
  set M := |C| / (ε / 3) + |b N1| + 1 with hM
  have hM_ge : ∀ᶠ n : ℕ in Filter.atTop, M ≤ b n :=
    hb_unbounded.eventually (Filter.eventually_ge_atTop M)
  rw [Filter.eventually_atTop] at hM_ge
  obtain ⟨N2, hN2⟩ := hM_ge
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hbn : M ≤ b n := hN2 n hn2
  have hbn_pos : 0 < b n := by
    have hnn : (0:ℝ) ≤ |C| / (ε / 3) + |b N1| := by positivity
    linarith
  -- per-term bound
  have hterm : ∀ k : ℕ, N1 ≤ k → k < n →
      |(a (k + 1) - a k) - L * (b (k + 1) - b k)| ≤ (ε / 3) * (b (k + 1) - b k) := by
    intro k hk1 _hk2
    have h := hN1 k hk1
    rw [dist_eq_norm, Real.norm_eq_abs] at h
    have hdk : (0:ℝ) < b (k + 1) - b k := hd_pos k
    have heq : (a (k + 1) - a k) - L * (b (k + 1) - b k) =
        ((a (k + 1) - a k) / (b (k + 1) - b k) - L) * (b (k + 1) - b k) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hdk]
    exact le_of_lt (mul_lt_mul_of_pos_right h hdk)
  -- telescoping identity
  have htele : (a n - L * b n) - (a N1 - L * b N1) =
      ∑ k ∈ Finset.Ico N1 n, ((a (k + 1) - a k) - L * (b (k + 1) - b k)) := by
    have e1 : ∑ k ∈ Finset.range n, ((a (k + 1) - a k) - L * (b (k + 1) - b k)) =
        (a n - L * b n) - (a 0 - L * b 0) := by
      have ha := Finset.sum_range_sub a n
      have hb := Finset.sum_range_sub b n
      have hL : (∑ k ∈ Finset.range n, (L * (b (k + 1) - b k))) =
          L * (∑ k ∈ Finset.range n, (b (k + 1) - b k)) := (Finset.mul_sum _ _ _).symm
      rw [Finset.sum_sub_distrib, hL, ha, hb]
      ring
    have e2 : ∑ k ∈ Finset.range N1, ((a (k + 1) - a k) - L * (b (k + 1) - b k)) =
        (a N1 - L * b N1) - (a 0 - L * b 0) := by
      have ha := Finset.sum_range_sub a N1
      have hb := Finset.sum_range_sub b N1
      have hL : (∑ k ∈ Finset.range N1, (L * (b (k + 1) - b k))) =
          L * (∑ k ∈ Finset.range N1, (b (k + 1) - b k)) := (Finset.mul_sum _ _ _).symm
      rw [Finset.sum_sub_distrib, hL, ha, hb]
      ring
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => ((a (k + 1) - a k) - L * (b (k + 1) - b k))) hn1
    linarith [e1, e2, hsplit]
  -- sum bound
  have hsum : |∑ k ∈ Finset.Ico N1 n, ((a (k + 1) - a k) - L * (b (k + 1) - b k))| ≤
      (ε / 3) * (b n - b N1) := by
    calc |∑ k ∈ Finset.Ico N1 n, ((a (k + 1) - a k) - L * (b (k + 1) - b k))|
        ≤ ∑ k ∈ Finset.Ico N1 n, |(a (k + 1) - a k) - L * (b (k + 1) - b k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico N1 n, (ε / 3) * (b (k + 1) - b k) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Ico] at hk
          exact hterm k hk.1 hk.2
      _ = (ε / 3) * (b n - b N1) := by
          rw [← Finset.mul_sum]
          congr 1
          have h1 := Finset.sum_range_sub b n
          have h2 := Finset.sum_range_sub b N1
          have hsplit := Finset.sum_range_add_sum_Ico (fun k => b (k + 1) - b k) hn1
          linarith
  -- combine
  have hCbound : |C| / b n < ε / 3 := by
    have h1 : |C| / (ε / 3) < b n := by
      have hnn : (0:ℝ) ≤ |b N1| := abs_nonneg _
      linarith [hbn]
    have hpos : (0:ℝ) < ε / 3 := by linarith
    have h2 : |C| < (ε / 3) * b n := by
      calc |C| = (|C| / (ε / 3)) * (ε / 3) := by field_simp
        _ < b n * (ε / 3) := mul_lt_mul_of_pos_right h1 hpos
        _ = (ε / 3) * b n := by ring
    calc |C| / b n < ((ε / 3) * b n) / b n :=
          div_lt_div_of_pos_right h2 hbn_pos
      _ = ε / 3 := by field_simp
  have hbN_bound : |b N1| ≤ b n := by
    have hnn : (0:ℝ) ≤ |C| / (ε / 3) := by positivity
    linarith [hbn]
  have hmain : |a n - L * b n| < ε * b n / 3 + (ε / 3) * (b n - b N1) := by
    have hC3 : |C| < ε * b n / 3 := by
      have h := hCbound
      rw [div_lt_iff₀ hbn_pos] at h
      linarith
    calc |a n - L * b n|
        = |(a n - L * b n) - C + C| := by congr 1; ring
      _ ≤ |(a n - L * b n) - C| + |C| := abs_add_le _ _
      _ = |∑ k ∈ Finset.Ico N1 n, ((a (k + 1) - a k) - L * (b (k + 1) - b k))| + |C| := by
          rw [htele, hC]
      _ ≤ (ε / 3) * (b n - b N1) + |C| := by gcongr
      _ < (ε / 3) * (b n - b N1) + ε * b n / 3 := by linarith [hC3]
      _ = ε * b n / 3 + (ε / 3) * (b n - b N1) := by ring
  rw [dist_eq_norm, Real.norm_eq_abs]
  have hdiv : a n / b n - L = (a n - L * b n) / b n := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hbn_pos]
  rw [div_lt_iff₀ hbn_pos]
  have hpos : (0:ℝ) < ε / 3 := by linarith
  have h4 : -(b N1) ≤ b n := by
    have h5 := neg_le_abs (b N1)
    linarith [h5, hbN_bound]
  have h6 : (ε / 3) * (-(b N1)) ≤ (ε / 3) * b n :=
    mul_le_mul_of_nonneg_left h4 (le_of_lt hpos)
  calc |a n - L * b n| < ε * b n / 3 + (ε / 3) * (b n - b N1) := hmain
    _ ≤ ε * b n / 3 + ((ε / 3) * b n + (ε / 3) * b n) := by linarith [h6]
    _ = ε * b n := by ring

end MetaMathlibExt

end
