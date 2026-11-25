/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 1

Series for log 2 - 1/2 via 1/(8n³-2n).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry1Corollary

open Filter Topology

private lemma term_eq (n : ℕ) :
    (1 : ℝ) / ((2 * (↑(n + 1) : ℝ)) ^ 3 - 2 * (↑(n + 1) : ℝ))
      = (1/2 : ℝ) * (-(1 / ((n : ℝ) + 1)) + 1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 3)) := by
  have hm : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have hcast : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h3 : (2 * ((n : ℝ) + 1) - 1) ≠ 0 := by
    have he : (2 : ℝ) * ((n : ℝ) + 1) - 1 = 2 * (n : ℝ) + 1 := by ring
    rw [he]; exact h1
  have h4 : (2 * ((n : ℝ) + 1) + 1) ≠ 0 := by
    have he : (2 : ℝ) * ((n : ℝ) + 1) + 1 = 2 * (n : ℝ) + 3 := by ring
    rw [he]; exact h2
  have hm2 : (2 * ((n : ℝ) + 1)) ≠ 0 := mul_ne_zero (by norm_num) hm
  have hden : (2 * ((n : ℝ) + 1)) ^ 3 - 2 * ((n : ℝ) + 1) ≠ 0 := by
    have hfac : (2 * ((n : ℝ) + 1)) ^ 3 - 2 * ((n : ℝ) + 1)
      = (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1) * (2 * ((n : ℝ) + 1) + 1) := by ring
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero hm2 h3) h4
  rw [div_eq_iff hden]
  field_simp
  ring

private lemma harmonic_succ_real (k : ℕ) :
    ((harmonic (k + 1) : ℚ) : ℝ) = ((harmonic k : ℚ) : ℝ) + 1 / (((k : ℝ) + 1)) := by
  have h := harmonic_succ k
  have hcast : ((harmonic (k+1) : ℚ) : ℝ) = ((harmonic k : ℚ) : ℝ) + ((((k+1 : ℕ) : ℚ) : ℝ))⁻¹ := by
    rw [h]
    push_cast
    ring
  rw [hcast]
  have hc : ((((k+1 : ℕ) : ℚ) : ℝ)) = ((k : ℝ) + 1) := by push_cast; ring
  rw [hc]
  rw [one_div]

private lemma partial_sum (N : ℕ) :
    ∑ n ∈ Finset.range N, ((1 : ℝ) / ((2 * (↑(n + 1) : ℝ)) ^ 3 - 2 * (↑(n + 1) : ℝ)))
    = (((harmonic (2 * N) : ℚ) : ℝ) + ((harmonic (2 * N + 1) : ℚ) : ℝ)
        - 2 * ((harmonic N : ℚ) : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, term_eq k]
    have hA : ((harmonic (2 * (k + 1)) : ℚ) : ℝ)
        = ((harmonic (2 * k + 1) : ℚ) : ℝ) + 1 / (2 * (k : ℝ) + 2) := by
      have hkk : (2 * (k + 1) : ℕ) = (2 * k + 1) + 1 := by ring
      rw [hkk, harmonic_succ_real]
      congr 1
      push_cast
      ring
    have hB : ((harmonic (2 * (k + 1) + 1) : ℚ) : ℝ)
        = ((harmonic (2 * (k + 1)) : ℚ) : ℝ) + 1 / (2 * (k : ℝ) + 3) := by
      have hkk : (2 * (k + 1) + 1 : ℕ) = (2 * (k + 1)) + 1 := by ring
      rw [hkk, harmonic_succ_real]
      congr 1
      push_cast
      ring
    have hC : ((harmonic (k + 1) : ℚ) : ℝ)
        = ((harmonic k : ℚ) : ℝ) + 1 / ((k : ℝ) + 1) := harmonic_succ_real k
    have hD : ((harmonic (2 * k + 1) : ℚ) : ℝ)
        = ((harmonic (2 * k) : ℚ) : ℝ) + 1 / (2 * (k : ℝ) + 1) := by
      have hkk : (2 * k + 1 : ℕ) = (2 * k) + 1 := by ring
      rw [hkk, harmonic_succ_real]
      congr 1
      push_cast
      ring
    rw [hB, hA, hC, hD]
    have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
    have hm : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h22 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

private lemma aux_summable : Summable (fun n : ℕ => (1 : ℝ) / ((2 * (↑(n + 1) : ℝ)) ^ 3 - 2 * (↑(n + 1) : ℝ))) := by
  have hmajor : Summable (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) ^ 3)) := by
    have h3 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 3)) :=
      (Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)
    have hshift := (summable_nat_add_iff (1 : ℕ)).mpr h3
    have heq : (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) ^ 3)) = (fun n : ℕ => 1 / ((((n + 1 : ℕ)) : ℝ) ^ 3)) := by
      funext n; push_cast; ring_nf
    rw [heq]
    exact hshift
  have hden_pos : ∀ n : ℕ, (0 : ℝ) < (2 * (↑(n + 1) : ℝ)) ^ 3 - 2 * (↑(n + 1) : ℝ) := by
    intro n
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcast : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hfac : (2 * ((n : ℝ) + 1)) ^ 3 - 2 * ((n : ℝ) + 1)
      = 2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1) * (2 * ((n : ℝ) + 1) + 1) := by ring
    rw [hfac]
    apply mul_pos (mul_pos _ _) _ <;> linarith
  apply Summable.of_nonneg_of_le (fun n => le_of_lt ?_) (fun n => ?_) hmajor
  · exact one_div_pos.mpr (hden_pos n)
  · have hcast : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    apply one_div_le_one_div_of_le (by positivity) ?_
    have hx0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hx1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hsq : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ hx1
    have h7 : (2 : ℝ) ≤ 7 * ((n : ℝ) + 1) ^ 2 := by linarith
    have hmul : (2 : ℝ) * ((n : ℝ) + 1) ≤ (7 * ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h7 hx0
    have h73 : (7 * ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1) = 7 * ((n : ℝ) + 1) ^ 3 := by ring
    have h8 : (2 * ((n : ℝ) + 1)) ^ 3 = 8 * ((n : ℝ) + 1) ^ 3 := by ring
    linarith

private lemma tendsto_two_mul_atTop : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  apply Filter.mem_of_superset (Filter.eventually_ge_atTop b) _
  intro N hN
  simp at hN ⊢
  omega

private lemma tendsto_two_mul_add_one_atTop : Filter.Tendsto (fun N : ℕ => 2 * N + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  apply Filter.mem_of_superset (Filter.eventually_ge_atTop b) _
  intro N hN
  simp at hN ⊢
  omega

private lemma log_two_mul_sub_log :
    Filter.Tendsto (fun N : ℕ => Real.log ((2 * N : ℕ) : ℝ) - Real.log ((N : ℕ) : ℝ))
    Filter.atTop (nhds (Real.log 2)) := by
  have heq : ∀ᶠ N : ℕ in Filter.atTop, Real.log ((2 * N : ℕ) : ℝ) - Real.log ((N : ℕ) : ℝ) = Real.log 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNne : ((N : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      omega
    have h2N : ((2 * N : ℕ) : ℝ) = 2 * ((N : ℕ) : ℝ) := by push_cast; ring
    rw [h2N, Real.log_mul (by norm_num) hNne]
    ring
  rw [Filter.tendsto_congr' heq]
  exact tendsto_const_nhds

private lemma log_two_mul_add_one_sub_log :
    Filter.Tendsto (fun N : ℕ => Real.log ((2 * N + 1 : ℕ) : ℝ) - Real.log ((N : ℕ) : ℝ))
    Filter.atTop (nhds (Real.log 2)) := by
  have hratio : Filter.Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ) / ((N : ℕ) : ℝ))
      Filter.atTop (nhds 2) := by
    have h2 : Filter.Tendsto (fun N : ℕ => (2 : ℝ) + 1 / ((N : ℕ) : ℝ))
        Filter.atTop (nhds (2 + 0)) :=
      Filter.Tendsto.add tendsto_const_nhds tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h2
    apply Filter.Tendsto.congr' _ h2
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNne : ((N : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      omega
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * ((N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    field_simp
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (((2 * N + 1 : ℕ) : ℝ) / ((N : ℕ) : ℝ)))
      Filter.atTop (nhds (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
  apply Filter.Tendsto.congr' _ hlog
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  have hpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg N
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * ((N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith
  have h2N1ne : ((2 * N + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
  exact Real.log_div h2N1ne hNne

private lemma rhs_tendsto :
    Filter.Tendsto (fun N : ℕ => (((harmonic (2 * N) : ℚ) : ℝ) + ((harmonic (2 * N + 1) : ℚ) : ℝ)
        - 2 * ((harmonic N : ℚ) : ℝ) - 1) / 2)
    Filter.atTop (nhds (Real.log 2 - 1 / 2)) := by
  have hA : Filter.Tendsto (fun N : ℕ => ((harmonic (2 * N) : ℚ) : ℝ) - Real.log ((2 * N : ℕ) : ℝ))
      Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp tendsto_two_mul_atTop
  have hB : Filter.Tendsto (fun N : ℕ => ((harmonic (2 * N + 1) : ℚ) : ℝ) - Real.log ((2 * N + 1 : ℕ) : ℝ))
      Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp tendsto_two_mul_add_one_atTop
  have hC : Filter.Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - Real.log ((N : ℕ) : ℝ))
      Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hAB := hA.add hB
  have h2C := hC.const_mul 2
  have hABC := hAB.sub h2C
  have hDE := log_two_mul_sub_log.add log_two_mul_add_one_sub_log
  have hABCDE := hABC.add hDE
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  have hABCDE1 := hABCDE.sub hone
  have hfinal := hABCDE1.div_const 2
  have hlim_eq : ((((Real.eulerMascheroniConstant + Real.eulerMascheroniConstant) - 2 * Real.eulerMascheroniConstant)
      + (Real.log 2 + Real.log 2)) - (1 : ℝ)) / 2 = Real.log 2 - 1 / 2 := by ring
  rw [hlim_eq] at hfinal
  exact hfinal.congr (fun N => by ring)

/-- **Ramanujan's series $\sum_{k \ge 1} 1/((2k)^3 - 2k) = \log 2 - 1/2$.** The series
$$\sum_{k=1}^{\infty} \frac{1}{(2k)^3 - 2k}$$
converges, and its sum is $\log 2 - \frac{1}{2}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2,
    corollary to Entry 1, printed p. 26 / PDF p. 36.
Proves `Wanted` entry `ramanujan_part1_ch2_entry1_corollary`.
-/
theorem ramanujan_part1_ch2_entry1_corollary :
    HasSum (fun n : ℕ => (1 : ℝ) / ((2 * (↑(n + 1) : ℝ)) ^ 3 - 2 * (↑(n + 1) : ℝ)))
        (Real.log 2 - 1 / 2) := by
  have hsumm := aux_summable
  rw [Summable.hasSum_iff_tendsto_nat hsumm]
  have h_eq : (fun N : ℕ => ∑ n ∈ Finset.range N,
      ((1 : ℝ) / ((2 * (↑(n + 1) : ℝ)) ^ 3 - 2 * (↑(n + 1) : ℝ))))
      = (fun N : ℕ => (((harmonic (2 * N) : ℚ) : ℝ) + ((harmonic (2 * N + 1) : ℚ) : ℝ)
        - 2 * ((harmonic N : ℚ) : ℝ) - 1) / 2) := funext fun N => partial_sum N
  rw [h_eq]
  exact rhs_tendsto

end Entry1Corollary

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
