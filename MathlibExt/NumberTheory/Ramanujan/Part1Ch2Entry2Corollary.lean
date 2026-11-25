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
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 2

Series for (log 3 - 1)/2 via 1/(27n³-3n).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry2Corollary

private lemma harm_succ_real (n : ℕ) :
    ((harmonic (n + 1) : ℚ) : ℝ) = ((harmonic n : ℚ) : ℝ) + 1 / ((n : ℝ) + 1) := by
  have h := harmonic_succ n
  have h2 : ((harmonic (n + 1) : ℚ) : ℝ) = ((harmonic n + ((n + 1 : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) := by rw [h]
  rw [h2]
  push_cast
  congr 1
  ring_nf

private lemma pf_id2 (n : ℝ) (hn : n ≠ 0) (h1 : 3 * n - 1 ≠ 0) (h2 : 3 * n + 1 ≠ 0) :
    1 / ((3 * n) ^ 3 - 3 * n)
      = -1 / (3 * n) + (1/2) * (1 / (3 * n - 1)) + (1/2) * (1 / (3 * n + 1)) := by
  have hfac : (3 * n) ^ 3 - 3 * n = 3 * n * (3 * n - 1) * (3 * n + 1) := by ring
  rw [hfac]
  field_simp
  ring

private lemma sum_ident (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1))
      = (((harmonic (3 * N + 1) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hn : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h1 : 3 * ((k : ℝ) + 1) - 1 ≠ 0 := by
      have h : 3 * ((k : ℝ) + 1) - 1 = 3 * (k : ℝ) + 2 := by ring
      rw [h]
      positivity
    have h2 : 3 * ((k : ℝ) + 1) + 1 ≠ 0 := by positivity
    rw [pf_id2 _ hn h1 h2]
    have e2 := harm_succ_real k
    have e1a := harm_succ_real (3 * k + 1)
    have e1b := harm_succ_real (3 * k + 1 + 1)
    have e1c := harm_succ_real (3 * k + 1 + 1 + 1)
    have hk1 : 3 * (k + 1) + 1 = (3 * k + 1 + 1 + 1) + 1 := by ring
    rw [hk1, e1c, e1b, e1a, e2]
    push_cast
    have d1 : 3 * ((k : ℝ) + 1) - 1 = (3 * (k : ℝ) + 1) + 1 := by ring
    have d2 : 3 * ((k : ℝ) + 1) + 1 = (3 * (k : ℝ) + 1) + 3 := by ring
    have d3 : 3 * ((k : ℝ) + 1) = (3 * (k : ℝ) + 1) + 2 := by ring
    rw [d1, d2, d3]
    have h33 : ((3 : ℝ) * (k : ℝ) + 1) + 2 ≠ 0 := by positivity
    have h_eq : ((3 : ℝ) * (k : ℝ) + 1) + 2 = 3 * ((k : ℝ) + 1) := by ring
    have e3 : (1 : ℝ) / ((k : ℝ) + 1) = 3 * (1 / (((3 : ℝ) * (k : ℝ) + 1) + 2)) := by
      rw [h_eq]
      field_simp
    rw [e3]
    ring

private lemma denom_pos (j : ℕ) : (0 : ℝ) < (3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1) := by
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  nlinarith [hj, sq_nonneg ((j : ℝ) + 1)]

private lemma term_le (j : ℕ) :
    (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1))
      ≤ 1 / ((((j : ℝ)) + 1) ^ 2) := by
  apply one_div_le_one_div_of_le (by positivity)
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  nlinarith [hj, sq_nonneg ((j : ℝ) + 1)]

private lemma summable_major : Summable (fun j : ℕ => (1 : ℝ) / ((((j : ℝ)) + 1) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) 1).mpr h2
  refine hshift.congr (fun j => ?_)
  simp

private lemma summable_target : Summable (fun j : ℕ => (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1))) := by
  apply Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) summable_major
  · exact le_of_lt (one_div_pos.mpr (denom_pos j))
  · exact term_le j

private lemma tend_3N1 : Filter.Tendsto (fun N : ℕ => 3 * N + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with N hN
  omega

private lemma tend_h3 : Filter.Tendsto (fun N : ℕ => ((harmonic (3 * N + 1) : ℚ) : ℝ) - Real.log (((3 * N + 1 : ℕ)) : ℝ)) Filter.atTop (nhds Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log.comp tend_3N1

private lemma logdiff_eq (N : ℕ) (hN : 1 ≤ N) :
    Real.log (((3 * N + 1 : ℕ)) : ℝ) - Real.log ((N : ℝ))
      = Real.log (3 + 1 / ((N : ℕ) : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := Nat.lt_of_lt_of_le (by norm_num) hN
    exact Nat.cast_pos.mpr this
  have h3N1 : (((3 * N + 1 : ℕ)) : ℝ) = 3 * (N : ℝ) + 1 := by push_cast; ring
  rw [h3N1]
  have hNe : ((N : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  have h3Ne : (3 : ℝ) * (N : ℝ) + 1 ≠ 0 := by positivity
  rw [← Real.log_div h3Ne hNe]
  congr 1
  field_simp

private lemma tend_logdiff : Filter.Tendsto (fun N : ℕ => Real.log (((3 * N + 1 : ℕ)) : ℝ) - Real.log ((N : ℕ) : ℝ)) Filter.atTop (nhds (Real.log 3)) := by
  have hcont : ContinuousAt Real.log 3 := Real.continuousAt_log (by norm_num)
  have h0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h3 : Filter.Tendsto (fun _ : ℕ => (3 : ℝ)) Filter.atTop (nhds 3) := tendsto_const_nhds
  have hinter : Filter.Tendsto (fun N : ℕ => (3 : ℝ) + 1 / ((N : ℕ) : ℝ)) Filter.atTop (nhds 3) := by
    have h := h3.add h0
    simpa [add_comm] using h
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (3 + 1 / ((N : ℕ) : ℝ))) Filter.atTop (nhds (Real.log 3)) :=
    hcont.tendsto.comp hinter
  apply Filter.Tendsto.congr' _ hlog
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN using (logdiff_eq N hN).symm

private lemma tend_partial :
    Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1)))
      Filter.atTop (nhds ((Real.log 3 - 1) / 2)) := by
  have hA := Real.tendsto_harmonic_sub_log
  have hC := tend_logdiff
  have hcomb : Filter.Tendsto (fun N : ℕ =>
      ((((harmonic (3 * N + 1) : ℚ) : ℝ) - Real.log (((3 * N + 1 : ℕ)) : ℝ))
        - (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ)))
        + (Real.log (((3 * N + 1 : ℕ)) : ℝ) - Real.log ((N : ℝ))) - 1) / 2)
      Filter.atTop (nhds ((Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + Real.log 3 - 1) / 2)) := by
    exact ((tend_h3.sub hA).add hC).sub_const 1 |>.div_const 2
  have hlim : (Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + Real.log 3 - 1) / 2 = (Real.log 3 - 1) / 2 := by ring
  rw [hlim] at hcomb
  have hcomb2 : Filter.Tendsto (fun N : ℕ => ((((harmonic (3 * N + 1) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ) - 1) / 2))
      Filter.atTop (nhds ((Real.log 3 - 1) / 2)) := by
    apply Filter.Tendsto.congr (fun N => ?_) hcomb
    ring
  exact Filter.Tendsto.congr (fun N => (sum_ident N).symm) hcomb2

/-- **Ramanujan's series $\sum_{k \ge 1} 1/((3k)^3 - 3k) = (\log 3 - 1)/2$.** The series
$$\sum_{k=1}^{\infty} \frac{1}{(3k)^3 - 3k}$$
converges, and its sum is $\frac{\log 3 - 1}{2}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2,
    corollary to Entry 2, printed p. 27 / PDF p. 37.
Proves `Wanted` entry `ramanujan_part1_ch2_entry2_corollary`.
-/
theorem ramanujan_part1_ch2_entry2_corollary :
    HasSum (fun j : ℕ => (1 : ℝ) / ((3 * ((j : ℝ) + 1)) ^ 3 - 3 * ((j : ℝ) + 1)))
        ((Real.log 3 - 1) / 2) := by
  exact summable_target.hasSum_iff_tendsto_nat.mpr tend_partial

end Entry2Corollary

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
