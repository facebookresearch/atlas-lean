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

theorem ons_riemann_periodic_average_of_tendstoUniformly
    (F : Nat → Real → Real) (f : Real → Real)
    (hf : Continuous f) (hper : Function.Periodic f (2 * Real.pi))
    (hF : TendstoUniformly F f atTop) :
    Tendsto (fun n : Nat =>
      (1 / (n : Real)) * ∑ k ∈ Finset.range n,
        F n (2 * Real.pi * k / n))
      atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ x in (0 : Real)..(2 * Real.pi), f x)) := by
  let T : Real := 2 * Real.pi
  have hT : 0 < T := by dsimp only [T]; positivity
  have hfixed := ons_riemann_periodic f hf hper
  have hdist : Tendsto (fun n : Nat =>
      dist
        ((T / n) * ∑ k ∈ Finset.range n, f (T * k / n))
        ((T / n) * ∑ k ∈ Finset.range n, F n (T * k / n)))
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
            (f (T * k / n) - F n (T * k / n))| ≤
          (T / n) * ∑ k ∈ Finset.range n,
            |f (T * k / n) - F n (T * k / n)| := by
        rw [abs_mul, abs_of_pos (div_pos hT hnR)]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (T / n) * ∑ _k ∈ Finset.range n, epsilon' := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hT.le hnR.le)
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_sub_comm, ← Real.dist_eq, dist_comm]
        exact (hcontrol _).le
      _ = T * epsilon' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [hn0]
      _ = epsilon / 2 := by
        dsimp only [epsilon']
        field_simp [hT.ne']
      _ < epsilon := by linarith
  have hvary := hfixed.congr_dist hdist
  have hmul := (tendsto_const_nhds : Tendsto
    (fun _ : Nat ↦ (1 / T : Real)) atTop (nhds (1 / T))).mul hvary
  convert hmul using 1
  · funext n
    by_cases hn : n = 0
    · simp [hn]
    · dsimp only [T]
      field_simp [hn, Real.pi_ne_zero]

theorem ons_riemann_periodic_shifted_average_of_tendstoUniformly
    (F : Nat → Real → Real) (f : Real → Real)
    (hf : Continuous f) (hper : Function.Periodic f (2 * Real.pi))
    (hF : TendstoUniformly F f atTop) :
    Tendsto (fun n : Nat =>
      (1 / (n : Real)) * ∑ k ∈ Finset.range n,
        F n (2 * Real.pi * k / n - Real.pi))
      atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ x in (-Real.pi)..Real.pi, f x)) := by
  let G : Nat → Real → Real := fun n x ↦ F n (x - Real.pi)
  let g : Real → Real := fun x ↦ f (x - Real.pi)
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro x
    dsimp only [g]
    convert hper (x - Real.pi) using 1 <;> ring
  have hG : TendstoUniformly G g atTop := by
    simpa only [G, g, Function.comp_apply] using
      hF.comp (fun x : Real ↦ x - Real.pi)
  have havg := ons_riemann_periodic_average_of_tendstoUniformly
    G g hg hgper hG
  have hint : (∫ x in (0 : Real)..(2 * Real.pi), g x) =
      ∫ x in (-Real.pi)..Real.pi, f x := by
    dsimp only [g]
    rw [intervalIntegral.integral_comp_sub_right]
    congr 1 <;> ring
  rw [hint] at havg
  simpa only [G] using havg

end StatMech.Onsager
