/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7, Example 2

Alternating sum of arctan(2/(n+k+1)²) equals arctan(1/(n²+n+1)).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Example2

private theorem arctan_sub_eq_aux2 (x y : ℝ) (h : x * (-y) < 1) :
    Real.arctan x - Real.arctan y = Real.arctan ((x - y) / (1 + x * y)) := by
  have h1 := Real.arctan_add h
  rw [Real.arctan_neg] at h1
  have he : (x + -y) / (1 - x * -y) = (x - y) / (1 + x * y) := by ring
  rw [he] at h1
  linarith [h1]

/-- **Alternating arctangent series (Entry 7, Example 2).** For every real number $n > 0$, the
series
$$\sum_{k=0}^{\infty} (-1)^k \arctan \frac{2}{(n + k + 1)^2}$$
converges absolutely and its sum is $\arctan \frac{1}{n^2 + n + 1}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    7, Example 2, formula (7.5), printed p. 36 / PDF p. 46.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_example2`.
-/
theorem ramanujan_part1_ch2_entry7_example2 (n : ℝ) (hn : 0 < n) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2))
        (Real.arctan (1 / (n ^ 2 + n + 1))) := by
  classical
  set a : ℕ → ℝ := fun k => Real.arctan (1 / (n + (k : ℝ))) with ha
  have hterm : ∀ k : ℕ, Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2) = a k - a (k + 2) := by
    intro k
    have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have hpos1 : (0:ℝ) < n + (k:ℝ) := by linarith
    have hpos2 : (0:ℝ) < n + (k:ℝ) + 2 := by linarith
    have hx : (0:ℝ) < 1 / (n + (k:ℝ)) := by positivity
    have hy : (0:ℝ) < 1 / (n + (k:ℝ) + 2) := by positivity
    have hcond : (1 / (n + (k:ℝ))) * (-(1 / (n + (k:ℝ) + 2))) < 1 := by
      have hlt : (1 / (n + (k:ℝ))) * (-(1 / (n + (k:ℝ) + 2))) < 0 :=
        mul_neg_of_pos_of_neg hx (neg_lt_zero.mpr hy)
      linarith
    have hsub := arctan_sub_eq_aux2 (1 / (n + (k:ℝ))) (1 / (n + (k:ℝ) + 2)) hcond
    have halg : ((1 / (n + (k:ℝ)) - 1 / (n + (k:ℝ) + 2)) /
        (1 + (1 / (n + (k:ℝ))) * (1 / (n + (k:ℝ) + 2))))
        = 2 / (n + (k : ℝ) + 1) ^ 2 := by
      have h1 : (n : ℝ) + (k : ℝ) ≠ 0 := ne_of_gt hpos1
      have h2 : (n : ℝ) + (k : ℝ) + 2 ≠ 0 := ne_of_gt hpos2
      field_simp
      ring
    rw [halg] at hsub
    have hak2 : a (k + 2) = Real.arctan (1 / (n + (k : ℝ) + 2)) := by
      simp only [ha]
      congr 1
      congr 1
      push_cast
      ring
    have hak : a k = Real.arctan (1 / (n + (k : ℝ))) := rfl
    rw [hak, hak2] at *
    exact hsub.symm
  have hnorm_sum : Summable (fun k : ℕ => ‖(-1 : ℝ) ^ k * Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2)‖) := by
    have hbase : Summable (fun m : ℕ => (1:ℝ)/((m:ℝ)^2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 : Summable (fun m : ℕ => (2:ℝ) * ((1:ℝ)/((m:ℝ)^2))) :=
      hbase.mul_left 2
    have hshift : Summable (fun k : ℕ => (2:ℝ) * ((1:ℝ)/((((k+1 : ℕ)):ℝ)^2))) :=
      (summable_nat_add_iff 1).mpr h2
    have hcomp : Summable (fun k : ℕ => (2:ℝ)/(((k:ℝ)+1)^2)) := by
      refine hshift.congr (fun k => ?_)
      have hcast : ((((k + 1 : ℕ)):ℝ)) = (k:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      ring
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hcomp
    have harg_nonneg : (0:ℝ) ≤ 2 / (n + (k : ℝ) + 1) ^ 2 := by positivity
    have h1 : ‖(-1 : ℝ) ^ k * Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2)‖
        ≤ 2 / (n + (k : ℝ) + 1) ^ 2 := by
      have heq : ‖(-1 : ℝ) ^ k * Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2)‖
          = |Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2)| := by
        rw [norm_mul]
        have hpow : ‖(-1 : ℝ) ^ k‖ = 1 := by simp
        rw [hpow, one_mul, Real.norm_eq_abs]
      rw [heq]
      calc |Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2)|
          ≤ |2 / (n + (k : ℝ) + 1) ^ 2| := Real.abs_arctan_le_abs
        _ = 2 / (n + (k : ℝ) + 1) ^ 2 := abs_of_nonneg harg_nonneg
    have hbase_le : ((k:ℝ)+1)^2 ≤ (n + (k : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _; linarith) 2
    have hpos_c : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
    have hle : (2:ℝ) / (n + (k : ℝ) + 1) ^ 2 ≤ 2 / (((k:ℝ)+1)^2) :=
      div_le_div_of_nonneg_left (by norm_num) hpos_c hbase_le
    linarith [h1, hle]
  have hpartial : ∀ N : ℕ, ∑ k ∈ Finset.range N, ((-1:ℝ)^k * (a k - a (k+2)))
      = a 0 - a 1 + (-1:ℝ)^(N+1) * a N + (-1:ℝ)^(N+2) * a (N+1) := by
    intro N
    induction N with
    | zero => simp; ring
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have g : (N : ℕ) + 2 = N + 1 + 1 := by ring
      rw [g]
      rw [pow_succ ((-1):ℝ) (N+1), pow_succ ((-1):ℝ) (N+2)]
      ring
  have hlim_a : Filter.Tendsto a Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (k:ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have htop : Filter.Tendsto (fun k : ℕ => n + (k:ℝ)) Filter.atTop Filter.atTop := by
      have h2 := Filter.tendsto_atTop_add_const_right Filter.atTop n h1
      simpa [add_comm] using h2
    have hdiv : Filter.Tendsto (fun k : ℕ => 1 / (n + (k:ℝ))) Filter.atTop (nhds 0) :=
      htop.const_div_atTop 1
    have hcont : ContinuousAt Real.arctan (0:ℝ) := Real.continuous_arctan.continuousAt
    have hcomp := hcont.tendsto.comp hdiv
    have hcomp' : Filter.Tendsto (fun k : ℕ => Real.arctan (1 / (n + (k:ℝ)))) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def, Real.arctan_zero] using hcomp
    simpa [ha] using hcomp'
  have halt : Filter.Tendsto (fun k : ℕ => (-1:ℝ)^k * a k) Filter.atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    have heq : (abs ∘ (fun k : ℕ => (-1:ℝ)^k * a k)) = (abs ∘ a) := by
      funext k
      simp [abs_mul]
    rw [heq]
    exact (tendsto_zero_iff_abs_tendsto_zero a).mp hlim_a
  have hR1 : Filter.Tendsto (fun N : ℕ => (-1:ℝ)^(N+1) * a N) Filter.atTop (nhds 0) := by
    have heq : (fun N : ℕ => (-1:ℝ)^(N+1) * a N) = (fun N : ℕ => -(((-1:ℝ)^N * a N))) := by
      funext N
      rw [pow_succ]
      ring
    rw [heq]
    simpa using halt.neg
  have hlim_a_succ : Filter.Tendsto (fun N : ℕ => a (N+1)) Filter.atTop (nhds 0) :=
    hlim_a.comp (Filter.tendsto_add_atTop_nat 1)
  have halt_succ : Filter.Tendsto (fun N : ℕ => (-1:ℝ)^N * a (N+1)) Filter.atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    have heq : (abs ∘ (fun N : ℕ => (-1:ℝ)^N * a (N+1))) = (abs ∘ (fun N : ℕ => a (N+1))) := by
      funext N
      simp [abs_mul]
    rw [heq]
    exact (tendsto_zero_iff_abs_tendsto_zero _).mp hlim_a_succ
  have hR2 : Filter.Tendsto (fun N : ℕ => (-1:ℝ)^(N+2) * a (N+1)) Filter.atTop (nhds 0) := by
    have heq : (fun N : ℕ => (-1:ℝ)^(N+2) * a (N+1)) = (fun N : ℕ => (-1:ℝ)^N * a (N+1)) := by
      funext N
      congr 1
      rw [pow_add]
      simp
    rw [heq]
    exact halt_succ
  have htarget : a 0 - a 1 = Real.arctan (1 / (n ^ 2 + n + 1)) := by
    have ha0 : a 0 = Real.arctan (1 / n) := by simp [ha]
    have ha1 : a 1 = Real.arctan (1 / (n + 1)) := by
      simp only [ha]
      congr 1
      congr 1
      push_cast
      ring
    rw [ha0, ha1]
    have hx : (0:ℝ) < 1 / n := by positivity
    have hy : (0:ℝ) < 1 / (n + 1) := by positivity
    have hcond : (1 / n) * (-(1 / (n + 1))) < 1 := by
      have hlt : (1 / n) * (-(1 / (n + 1))) < 0 :=
        mul_neg_of_pos_of_neg hx (neg_lt_zero.mpr hy)
      linarith
    have hsub := arctan_sub_eq_aux2 (1 / n) (1 / (n + 1)) hcond
    have halg : ((1 / n - 1 / (n + 1)) / (1 + (1 / n) * (1 / (n + 1))))
        = 1 / (n ^ 2 + n + 1) := by
      have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hn
      have hn1 : (n:ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [halg] at hsub
    exact hsub
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm_sum).mpr
  have hsum_eq : (fun N : ℕ => ∑ k ∈ Finset.range N, ((-1:ℝ)^k * Real.arctan (2 / (n + (k:ℝ) + 1)^2)))
      = (fun N : ℕ => ∑ k ∈ Finset.range N, ((-1:ℝ)^k * (a k - a (k+2)))) := by
    funext N
    apply Finset.sum_congr rfl
    intro k _
    rw [hterm k]
  rw [hsum_eq]
  have hlim_sum : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, ((-1:ℝ)^k * (a k - a (k+2)))) Filter.atTop (nhds (a 0 - a 1)) := by
    have heq : (fun N : ℕ => ∑ k ∈ Finset.range N, ((-1:ℝ)^k * (a k - a (k+2))))
        = (fun N : ℕ => (a 0 - a 1) + ((-1:ℝ)^(N+1) * a N + (-1:ℝ)^(N+2) * a (N+1))) := by
      funext N
      rw [hpartial N]
      ring
    rw [heq]
    have hadd : Filter.Tendsto (fun N : ℕ => (-1:ℝ)^(N+1) * a N + (-1:ℝ)^(N+2) * a (N+1)) Filter.atTop (nhds (0+0)) :=
      hR1.add hR2
    simpa using tendsto_const_nhds.add hadd
  rw [htarget] at hlim_sum
  exact hlim_sum

end Entry7Example2

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
