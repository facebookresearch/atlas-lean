/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.RiemannPeriodic





open scoped BigOperators Real
open MeasureTheory Filter

namespace StatMech.Onsager



theorem ons_riemann_periodic_midpoint (f : Real → Real) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    Tendsto (fun n : Nat =>
      (2 * Real.pi / n) * ∑ k ∈ Finset.range n,
        f (2 * Real.pi * (k + (1 : Real) / 2) / n - Real.pi))
      atTop
      (nhds (∫ x in (-Real.pi)..Real.pi, f x)) := by
  let T : Real := 2 * Real.pi
  let g : Real → Real := fun x ↦ f (x - Real.pi)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hgper : Function.Periodic g T := by
    intro x
    dsimp only [g, T]
    convert hper (x - Real.pi) using 1 <;> ring
  have hleft := ons_riemann_periodic g hg hgper
  have hint : (∫ x in (0 : Real)..T, g x) =
      ∫ x in (-Real.pi)..Real.pi, f x := by
    dsimp only [g, T]
    rw [intervalIntegral.integral_comp_sub_right]
    congr 1 <;> ring
  rw [hint] at hleft
  have hdist : Tendsto (fun n : Nat =>
      dist
        ((T / n) * ∑ k ∈ Finset.range n, g (T * k / n))
        ((T / n) * ∑ k ∈ Finset.range n,
          g (T * (k + (1 : Real) / 2) / n)))
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let epsilon' := epsilon / (2 * T)
    have hepsilon' : 0 < epsilon' := by
      dsimp only [epsilon']
      positivity
    have hucon : UniformContinuousOn g (Set.Icc (0 : Real) T) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
    obtain ⟨delta, hdelta, hcontrol⟩ :=
      (Metric.uniformContinuousOn_iff.mp hucon) epsilon' hepsilon'
    obtain ⟨N, hN⟩ := exists_nat_gt (T / (2 * delta))
    refine ⟨max N 1, fun n hn ↦ ?_⟩
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : 0 < (n : Real) := by exact_mod_cast hn1
    have hn0 : (n : Real) ≠ 0 := hnR.ne'
    have hmesh : T / (2 * n) < delta := by
      rw [div_lt_iff₀ (mul_pos (by norm_num) hnR)]
      have hnLarge : T / (2 * delta) < (n : Real) :=
        lt_of_lt_of_le hN (by exact_mod_cast hnN)
      rw [div_lt_iff₀ (mul_pos (by norm_num) hdelta)] at hnLarge
      nlinarith
    rw [Real.dist_eq]
    simp only [sub_zero, abs_of_nonneg dist_nonneg]
    rw [Real.dist_eq, ← mul_sub, ← Finset.sum_sub_distrib]
    have hterm (k : Nat) (hk : k ∈ Finset.range n) :
        |g (T * k / n) - g (T * (k + (1 : Real) / 2) / n)| < epsilon' := by
      have hkn := Finset.mem_range.mp hk
      have hkR : (k : Real) ≤ n := by exact_mod_cast hkn.le
      have hkHalfR : (k : Real) + 1 / 2 ≤ n := by
        have hk1R : (k : Real) + 1 ≤ n := by
          exact_mod_cast (Nat.succ_le_iff.mpr hkn)
        linarith
      have hxmem : T * (k : Real) / n ∈ Set.Icc (0 : Real) T := by
        constructor
        · positivity
        · rw [div_le_iff₀ hnR]
          nlinarith
      have hymem : T * ((k : Real) + 1 / 2) / n ∈ Set.Icc (0 : Real) T := by
        constructor
        · positivity
        · rw [div_le_iff₀ hnR]
          nlinarith
      have hxy : dist (T * (k : Real) / n)
          (T * ((k : Real) + 1 / 2) / n) < delta := by
        rw [Real.dist_eq]
        have heq : T * (k : Real) / n -
            T * ((k : Real) + 1 / 2) / n = -(T / (2 * n)) := by
          field_simp [hn0]
          ring
        rw [heq, abs_neg, abs_of_pos (div_pos hT (mul_pos (by norm_num) hnR))]
        exact hmesh
      simpa [Real.dist_eq] using hcontrol _ hxmem _ hymem hxy
    calc
      |T / (n : Real) *
          ∑ k ∈ Finset.range n,
            (g (T * k / n) - g (T * (k + (1 : Real) / 2) / n))| ≤
          (T / n) * ∑ k ∈ Finset.range n,
            |g (T * k / n) - g (T * (k + (1 : Real) / 2) / n)| := by
        rw [abs_mul, abs_of_pos (div_pos hT hnR)]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (T / n) * ∑ _k ∈ Finset.range n, epsilon' := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hT.le hnR.le)
        exact Finset.sum_le_sum fun k hk ↦ (hterm k hk).le
      _ = T * epsilon' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [hn0]
      _ = epsilon / 2 := by
        dsimp only [epsilon']
        field_simp [hT.ne']
      _ < epsilon := by linarith
  have hmid := hleft.congr_dist hdist
  simpa only [T, g, mul_div_assoc] using hmid



theorem ons_riemann_periodic_midpoint_of_tendstoUniformly
    (F : Nat → Real → Real) (f : Real → Real)
    (hf : Continuous f) (hper : Function.Periodic f (2 * Real.pi))
    (hF : TendstoUniformly F f atTop) :
    Tendsto (fun n : Nat =>
      (2 * Real.pi / n) * ∑ k ∈ Finset.range n,
        F n (2 * Real.pi * (k + (1 : Real) / 2) / n - Real.pi))
      atTop (nhds (∫ x in (-Real.pi)..Real.pi, f x)) := by
  let T : Real := 2 * Real.pi
  have hT : 0 < T := by dsimp only [T]; positivity
  have hfixed := ons_riemann_periodic_midpoint f hf hper
  have hdist : Tendsto (fun n : Nat =>
      dist
        ((T / n) * ∑ k ∈ Finset.range n,
          f (T * (k + (1 : Real) / 2) / n - Real.pi))
        ((T / n) * ∑ k ∈ Finset.range n,
          F n (T * (k + (1 : Real) / 2) / n - Real.pi)))
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let epsilon' := epsilon / (2 * T)
    have hepsilon' : 0 < epsilon' := by
      dsimp only [epsilon']
      positivity
    have hev := (Metric.tendstoUniformly_iff.mp hF) epsilon' hepsilon'
    rw [eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨max N 1, fun n hn ↦ ?_⟩
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : 0 < (n : Real) := by exact_mod_cast hn1
    have hn0 : (n : Real) ≠ 0 := hnR.ne'
    have hcontrol := hN n hnN
    rw [Real.dist_eq]
    simp only [sub_zero, abs_of_nonneg dist_nonneg]
    rw [Real.dist_eq, ← mul_sub, ← Finset.sum_sub_distrib]
    calc
      |T / (n : Real) *
          ∑ k ∈ Finset.range n,
            (f (T * (k + (1 : Real) / 2) / n - Real.pi) -
              F n (T * (k + (1 : Real) / 2) / n - Real.pi))| ≤
          (T / n) * ∑ k ∈ Finset.range n,
            |f (T * (k + (1 : Real) / 2) / n - Real.pi) -
              F n (T * (k + (1 : Real) / 2) / n - Real.pi)| := by
        rw [abs_mul, abs_of_pos (div_pos hT hnR)]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (T / n) * ∑ _k ∈ Finset.range n, epsilon' := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hT.le hnR.le)
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_sub_comm, ← Real.dist_eq]
        rw [dist_comm]
        exact (hcontrol _).le
      _ = T * epsilon' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [hn0]
      _ = epsilon / 2 := by
        dsimp only [epsilon']
        field_simp [hT.ne']
      _ < epsilon := by linarith
  have hvary := hfixed.congr_dist hdist
  simpa only [T, mul_div_assoc] using hvary

theorem ons_riemann_periodic_midpoint_average_of_tendstoUniformly
    (F : Nat → Real → Real) (f : Real → Real)
    (hf : Continuous f) (hper : Function.Periodic f (2 * Real.pi))
    (hF : TendstoUniformly F f atTop) :
    Tendsto (fun n : Nat =>
      (1 / (n : Real)) * ∑ k ∈ Finset.range n,
        F n (2 * Real.pi * (k + (1 : Real) / 2) / n - Real.pi))
      atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ x in (-Real.pi)..Real.pi, f x)) := by
  have hscaled := ons_riemann_periodic_midpoint_of_tendstoUniformly
    F f hf hper hF
  have hmul := (tendsto_const_nhds : Tendsto
    (fun _ : Nat ↦ (1 / (2 * Real.pi) : Real)) atTop
    (nhds (1 / (2 * Real.pi)))).mul hscaled
  convert hmul using 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · field_simp [hn, Real.pi_ne_zero]

end StatMech.Onsager
