/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Complex.NormalFamilies

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

section
namespace MathlibExt.Analysis.Complex.JentzschPowerSeriesWanted

private theorem eval_trunc_succ_mk_eq_sum (a : ℕ → ℂ) (n : ℕ) (w : ℂ) :
    Polynomial.eval w (PowerSeries.trunc (n + 1) (PowerSeries.mk a))
      = ∑ k ∈ Finset.range (n + 1), a k * w ^ k := by
  have h : Polynomial.eval w (PowerSeries.trunc (n + 1) (PowerSeries.mk a))
      = Polynomial.eval₂ (RingHom.id ℂ) w (PowerSeries.trunc (n + 1) (PowerSeries.mk a)) := by
    rw [Polynomial.eval₂_id]
  rw [h, PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp [PowerSeries.coeff_mk]

private theorem section_succ_sub (a : ℕ → ℂ) (m : ℕ) (w : ℂ) :
    (∑ k ∈ Finset.range (m + 1 + 1), a k * w ^ k) - (∑ k ∈ Finset.range (m + 1), a k * w ^ k)
      = a (m + 1) * w ^ (m + 1) := by
  rw [Finset.sum_range_succ]
  ring

private theorem aux_geom (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (4 : ℝ) ^ k ≤ 2 * 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h4 : (4:ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
    have h4n : (0:ℝ) ≤ 4 ^ n := by positivity
    linarith [ih]

private theorem norm_section_le_of_radius (a : ℕ → ℂ)
    (h : 1 ≤ (FormalMultilinearSeries.ofScalars Complex a).radius) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∀ w : ℂ, ‖w‖ ≤ 2 →
      ‖∑ k ∈ Finset.range (n + 1), a k * w ^ k‖ ≤ C * 4 ^ n := by
  set p := FormalMultilinearSeries.ofScalars Complex a with hp
  have hlt : ((1 / 2 : ℝ≥0) : ℝ≥0∞) < p.radius := by
    have h1 : ((1 / 2 : ℝ≥0) : ℝ≥0∞) < 1 := by
      rw [ENNReal.coe_lt_one_iff]
      norm_num
    exact lt_of_lt_of_le h1 h
  obtain ⟨C0, hC0pos, hC0⟩ :=
    FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius p hlt
  have hCoeff : ∀ k : ℕ, ‖a k‖ ≤ C0 * 2 ^ k := by
    intro k
    have hk := hC0 k
    rw [FormalMultilinearSeries.ofScalars_norm] at hk
    have hr : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by
      simp
    rw [hr] at hk
    have h2k : (0:ℝ) < 2 ^ k := by positivity
    have hmul : ((1 / 2 : ℝ)) ^ k * 2 ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    have hcalc : ‖a k‖ = (‖a k‖ * (1 / 2) ^ k) * 2 ^ k := by
      rw [mul_assoc, hmul, mul_one]
    rw [hcalc]
    apply mul_le_mul_of_nonneg_right hk (le_of_lt h2k)
  refine ⟨max (2 * C0) 1, le_max_right _ _, ?_⟩
  intro n w hw
  have h4n : (0:ℝ) ≤ 4 ^ n := by positivity
  have hC0nn : (0:ℝ) ≤ C0 := le_of_lt hC0pos
  have hpow : ∀ k : ℕ, (C0 * 2 ^ k) * 2 ^ k = C0 * (4:ℝ) ^ k := by
    intro k
    have h44 : (4:ℝ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    rw [h44]
    ring
  calc ‖∑ k ∈ Finset.range (n + 1), a k * w ^ k‖
      ≤ ∑ k ∈ Finset.range (n + 1), ‖a k * w ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), C0 * 4 ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, norm_pow, ← hpow k]
        apply mul_le_mul (hCoeff k) (pow_le_pow_left₀ (norm_nonneg _) hw k)
          (by positivity) (by positivity)
    _ = C0 * (∑ k ∈ Finset.range (n + 1), (4:ℝ) ^ k) := by rw [Finset.mul_sum]
    _ ≤ C0 * (2 * 4 ^ n) := by
        apply mul_le_mul_of_nonneg_left (aux_geom n) hC0nn
    _ ≤ max (2 * C0) 1 * 4 ^ n := by
        have hle : C0 * 2 ≤ max (2 * C0) 1 := by
          calc C0 * 2 = 2 * C0 := by ring
            _ ≤ max (2 * C0) 1 := le_max_left _ _
        calc C0 * (2 * 4 ^ n) = (C0 * 2) * 4 ^ n := by ring
          _ ≤ max (2 * C0) 1 * 4 ^ n :=
              mul_le_mul_of_nonneg_right hle h4n

private theorem one_lt_radius_of_eventually_norm_section_le (a : ℕ → ℂ) (q : ℂ) (η : ℝ)
    (hη : 0 ≤ η) (hq : 1 + η < ‖q‖)
    (h : ∀ᶠ n in atTop, ‖∑ k ∈ Finset.range (n + 1), a k * q ^ k‖ ≤ (1 + η) ^ n) :
    1 < (FormalMultilinearSeries.ofScalars Complex a).radius := by
  set R : ℝ := 1 + η with hR
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hRnn : 0 ≤ R := le_of_lt hRpos
  have hqpos : 0 < ‖q‖ := lt_trans hRpos hq
  have hsuc : ∀ᶠ m in atTop, ‖∑ k ∈ Finset.range (m + 1 + 1), a k * q ^ k‖ ≤ R ^ (m + 1) := by
    have hcomp : Filter.Tendsto (fun m : ℕ => m + 1) atTop atTop :=
      Filter.tendsto_add_atTop_iff_nat 1 |>.mpr tendsto_id
    have h2 := hcomp.eventually h
    simpa [hR] using h2
  have hboth : ∀ᶠ m in atTop,
      (‖∑ k ∈ Finset.range (m + 1), a k * q ^ k‖ ≤ R ^ m) ∧
      (‖∑ k ∈ Finset.range (m + 1 + 1), a k * q ^ k‖ ≤ R ^ (m + 1)) := by
    have hR' : ∀ᶠ m in atTop, ‖∑ k ∈ Finset.range (m + 1), a k * q ^ k‖ ≤ R ^ m := by
      simpa [hR] using h
    exact hR'.and hsuc
  have hdiff : ∀ᶠ m in atTop, ‖a (m + 1) * q ^ (m + 1)‖ ≤ 2 * R ^ (m + 1) := by
    filter_upwards [hboth] with m hm
    have hdeq : (∑ k ∈ Finset.range (m + 1 + 1), a k * q ^ k)
        - (∑ k ∈ Finset.range (m + 1), a k * q ^ k) = a (m + 1) * q ^ (m + 1) := by
      rw [Finset.sum_range_succ]
      ring
    have hle : R ^ m ≤ R ^ (m + 1) := pow_le_pow_right₀ hR1 (Nat.le_succ _)
    calc ‖a (m + 1) * q ^ (m + 1)‖
        = ‖(∑ k ∈ Finset.range (m + 1 + 1), a k * q ^ k)
          - (∑ k ∈ Finset.range (m + 1), a k * q ^ k)‖ := by rw [hdeq]
      _ ≤ ‖∑ k ∈ Finset.range (m + 1 + 1), a k * q ^ k‖
          + ‖∑ k ∈ Finset.range (m + 1), a k * q ^ k‖ := norm_sub_le _ _
      _ ≤ R ^ (m + 1) + R ^ m := by linarith [hm.1, hm.2]
      _ ≤ R ^ (m + 1) + R ^ (m + 1) := by linarith
      _ = 2 * R ^ (m + 1) := by ring
  set rho : ℝ≥0 := ⟨‖q‖ / R, div_nonneg (norm_nonneg _) hRnn⟩ with hrho
  have hrho_coe : (rho : ℝ) = ‖q‖ / R := rfl
  have hrho_gt_one : 1 < rho := by
    rw [← NNReal.coe_lt_coe]
    simp only [NNReal.coe_one, hrho_coe]
    rw [lt_div_iff₀ hRpos]
    linarith [hq]
  have hcoeff_succ : ∀ᶠ m in atTop,
      ‖a (m + 1)‖ * (rho : ℝ) ^ (m + 1) ≤ 2 := by
    filter_upwards [hdiff] with m hm
    rw [norm_mul, norm_pow] at hm
    have hRpow_pos : (0:ℝ) < R ^ (m + 1) := by positivity
    have hdiv : (rho : ℝ) ^ (m + 1) = ‖q‖ ^ (m + 1) / R ^ (m + 1) := by
      rw [hrho_coe, div_pow]
    rw [hdiv, ← mul_div_assoc, div_le_iff₀ hRpow_pos]
    linarith [hm]
  have hcoeff : ∀ᶠ n in atTop, ‖a n‖ * (rho : ℝ) ^ n ≤ 2 := by
    rw [Filter.eventually_atTop] at hcoeff_succ ⊢
    obtain ⟨K, hK⟩ := hcoeff_succ
    refine ⟨K + 1, fun n hn => ?_⟩
    have hm : n - 1 ≥ K := by omega
    have hKm := hK (n - 1) hm
    have hnm : (n - 1) + 1 = n := by omega
    rwa [hnm] at hKm
  have hrad : (rho : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars Complex a).radius := by
    apply FormalMultilinearSeries.le_radius_of_eventually_le _ 2
    filter_upwards [hcoeff] with n hn
    have hn2 : ‖(FormalMultilinearSeries.ofScalars Complex a) n‖ * (rho : ℝ) ^ n ≤ 2 := by
      rw [FormalMultilinearSeries.ofScalars_norm]
      exact hn
    exact hn2
  have h1lt : (1 : ℝ≥0∞) < (rho : ℝ≥0∞) := by
    rw [ENNReal.one_lt_coe_iff]
    exact hrho_gt_one
  calc (1 : ℝ≥0∞) < (rho : ℝ≥0∞) := h1lt
    _ ≤ _ := hrad

private theorem tendsto_section_of_norm_lt_one (a : ℕ → ℂ)
    (hradius : (FormalMultilinearSeries.ofScalars Complex a).radius = 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k * z ^ k) atTop
      (𝓝 ((FormalMultilinearSeries.ofScalars Complex a).sum z)) := by
  set p := FormalMultilinearSeries.ofScalars Complex a with hp
  have hzmem : z ∈ Metric.eball 0 p.radius := by
    rw [hradius, mem_eball_zero_iff, enorm_eq_nnnorm]
    exact_mod_cast hz
  have hHas : HasSum (fun k => p k (fun _ => z)) (p.sum z) :=
    FormalMultilinearSeries.hasSum p hzmem
  have hTend : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, p k (fun _ => z)) atTop
      (𝓝 (p.sum z)) := hHas.tendsto_sum_nat
  have heq : (fun n => ∑ k ∈ Finset.range (n + 1), a k * z ^ k)
      = (fun n => ∑ k ∈ Finset.range (n + 1), p k (fun _ => z)) := by
    funext n
    apply Finset.sum_congr rfl
    intro k _
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [heq]
  have h2 : Filter.Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), p k (fun _ => z)) atTop
      (𝓝 (p.sum z)) := by
    have := hTend.comp (Filter.tendsto_add_atTop_iff_nat 1 |>.mpr tendsto_id)
    simpa [Function.comp_def, Nat.add_comm] using this
  exact h2

private theorem eball_one_eq_ball_one : Metric.eball (0:ℂ) 1 = Metric.ball (0:ℂ) 1 := by
  have h1 : (1 : ENNReal) = ((1 : NNReal) : ENNReal) := by simp
  rw [h1, Metric.eball_coe]
  norm_num

private theorem continuousOn_sum_of_radius (a : ℕ → ℂ)
    (hradius : (FormalMultilinearSeries.ofScalars Complex a).radius = 1) :
    ContinuousOn (FormalMultilinearSeries.ofScalars Complex a).sum (Metric.ball 0 1) := by
  set p := FormalMultilinearSeries.ofScalars Complex a with hp
  have hpos : 0 < p.radius := by rw [hradius]; norm_num
  have hball := (FormalMultilinearSeries.hasFPowerSeriesOnBall p hpos).continuousOn
  rw [hradius, eball_one_eq_ball_one] at hball
  exact hball

private theorem exists_sum_ne_zero_of_isOpen (a : ℕ → ℂ)
    (hradius : (FormalMultilinearSeries.ofScalars Complex a).radius = 1)
    (U : Set ℂ) (hUopen : IsOpen U) (hUne : U.Nonempty) (hUsub : U ⊆ Metric.ball 0 1) :
    ∃ c ∈ U, (FormalMultilinearSeries.ofScalars Complex a).sum c ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ c ∈ U, (FormalMultilinearSeries.ofScalars Complex a).sum c = 0 := by
    intro c hc
    by_contra hne
    exact hcon ⟨c, hc, hne⟩
  set p := FormalMultilinearSeries.ofScalars Complex a with hp
  have hpos : 0 < p.radius := by rw [hradius]; norm_num
  have hFP := FormalMultilinearSeries.hasFPowerSeriesOnBall p hpos
  have hana : AnalyticOnNhd ℂ p.sum (Metric.ball 0 1) := by
    have h2 := hFP.analyticOnNhd
    rwa [hradius, eball_one_eq_ball_one] at h2
  obtain ⟨u, huU⟩ := hUne
  have huBall : u ∈ Metric.ball 0 1 := hUsub huU
  have hev : p.sum =ᶠ[𝓝 u] 0 := by
    filter_upwards [hUopen.mem_nhds huU] with z hz
    exact hcon' z hz
  have heqOn : Set.EqOn p.sum 0 (Metric.ball 0 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hana
      (convex_ball 0 1).isPreconnected huBall hev
  have h0mem : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
  have hev0 : p.sum =ᶠ[𝓝 (0:ℂ)] 0 := by
    have hmem : Metric.ball 0 1 ∈ 𝓝 (0:ℂ) := Metric.isOpen_ball.mem_nhds h0mem
    filter_upwards [hmem] with z hz
    exact heqOn hz
  have hat : HasFPowerSeriesAt p.sum p 0 := hFP.hasFPowerSeriesAt
  have hpeq : p = 0 := hat.eq_zero_of_eventually hev0
  have haeq : a = 0 := by
    have := (FormalMultilinearSeries.ofScalars_series_eq_zero Complex).mp hpeq
    exact this
  have htop : p.radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
    filter_upwards with n
    simp [hp, haeq]
  rw [hradius] at htop
  simp at htop

private theorem eq_one_of_pow_bounds (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k) (N₀ : ℕ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (L : ℝ)
    (hL : Filter.Tendsto (fun j => x (φ j)) atTop (𝓝 L))
    (m : ℝ) (hm : 0 < m) (M : ℝ)
    (hb : ∀ᶠ k in atTop, m ≤ x k ^ (k + N₀) ∧ x k ^ (k + N₀) ≤ M) : L = 1 := by
  have hLnn : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun j => hx (φ j))
  have hbphi : ∀ᶠ j in atTop, m ≤ x (φ j) ^ (φ j + N₀) ∧ x (φ j) ^ (φ j + N₀) ≤ M :=
    hφ.tendsto_atTop.eventually hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with hLt | hGt
  · obtain ⟨lam, hLlam, hlam1⟩ : ∃ lam : ℝ, L < lam ∧ lam < 1 := exists_between hLt
    have hlamnn : 0 ≤ lam := le_trans hLnn (le_of_lt hLlam)
    have hev : ∀ᶠ j in atTop, x (φ j) < lam := hL.eventually_lt_const hLlam
    have hevle : ∀ᶠ j in atTop, x (φ j) ^ (φ j + N₀) ≤ lam ^ (φ j + N₀) := by
      filter_upwards [hev] with j hj
      exact pow_le_pow_left₀ (hx _) (le_of_lt hj) _
    have htop : Filter.Tendsto (fun j => φ j + N₀) atTop atTop := by
      apply Filter.tendsto_atTop_mono (fun j => Nat.le_add_right _ _)
      exact hφ.tendsto_atTop
    have hexp : Filter.Tendsto (fun j => lam ^ (φ j + N₀)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hlamnn hlam1).comp htop
    have hltm : ∀ᶠ j in atTop, lam ^ (φ j + N₀) < m := hexp.eventually_lt_const hm
    have hall : ∀ᶠ j in atTop, m ≤ x (φ j) ^ (φ j + N₀) ∧ x (φ j) ^ (φ j + N₀) < m := by
      filter_upwards [hbphi, hevle, hltm] with j h1 h2 h3
      exact ⟨h1.1, lt_of_le_of_lt h2 h3⟩
    obtain ⟨j, hj⟩ := hall.exists
    linarith [hj.1, hj.2]
  · obtain ⟨lam, h1lam, hllam⟩ : ∃ lam : ℝ, 1 < lam ∧ lam < L := exists_between hGt
    have hev : ∀ᶠ j in atTop, lam < x (φ j) := hL.eventually_const_lt hllam
    have htop : Filter.Tendsto (fun j => φ j + N₀) atTop atTop := by
      apply Filter.tendsto_atTop_mono (fun j => Nat.le_add_right _ _)
      exact hφ.tendsto_atTop
    have hexp : Filter.Tendsto (fun j => lam ^ (φ j + N₀)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt h1lam).comp htop
    have hlamnn : (0:ℝ) ≤ lam := zero_le_one.trans h1lam.le
    have hevge : ∀ᶠ j in atTop, lam ^ (φ j + N₀) ≤ x (φ j) ^ (φ j + N₀) := by
      filter_upwards [hev] with j hj
      exact pow_le_pow_left₀ hlamnn (le_of_lt hj) _
    have hgtM : ∀ᶠ j in atTop, M < lam ^ (φ j + N₀) := by
      have h2 := hexp.eventually_ge_atTop (M + 1)
      filter_upwards [h2] with j hj
      linarith
    have hall : ∀ᶠ j in atTop, x (φ j) ^ (φ j + N₀) ≤ M ∧ M < x (φ j) ^ (φ j + N₀) := by
      filter_upwards [hbphi, hevge, hgtM] with j h1 h2 h3
      exact ⟨h1.2, lt_of_lt_of_le h3 h2⟩
    obtain ⟨j, hj⟩ := hall.exists
    linarith [hj.1, hj.2]

private theorem norm_eq_one_on_ball_of_norm_eq_one_near (ψ : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hψ : DifferentiableOn ℂ ψ (Metric.ball c r)) (x : ℂ) (hx : x ∈ Metric.ball c r)
    (hev : ∀ᶠ z in 𝓝 x, ‖ψ z‖ = 1) :
    ∀ z ∈ Metric.ball c r, ‖ψ z‖ = 1 := by
  have hopen : IsOpen (Metric.ball c r) := Metric.isOpen_ball
  have hball_nhds : Metric.ball c r ∈ 𝓝 x := hopen.mem_nhds hx
  have hdiff_at : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ ψ z := by
    filter_upwards [hball_nhds] with z hz
    exact hψ.differentiableAt (hopen.mem_nhds hz)
  have hcont : ContinuousAt ψ x := hψ.continuousOn.continuousAt hball_nhds
  have hnorm_tend : Filter.Tendsto (fun z => ‖ψ z‖) (𝓝 x) (𝓝 ‖ψ x‖) :=
    (hcont.tendsto).norm
  have hlim1 : Filter.Tendsto (fun z => ‖ψ z‖) (𝓝 x) (𝓝 1) := by
    have hconst : Filter.Tendsto (fun _ : ℂ => (1 : ℝ)) (𝓝 x) (𝓝 1) := tendsto_const_nhds
    apply Tendsto.congr' _ hconst
    filter_upwards [hev] with z hz using hz.symm
  have hxval : ‖ψ x‖ = 1 := tendsto_nhds_unique hnorm_tend hlim1
  have hmax : IsLocalMax (norm ∘ ψ) x := by
    filter_upwards [hev] with z hz
    simp [Function.comp_apply, hxval, hz]
  have heq : ψ =ᶠ[𝓝 x] fun _ => ψ x :=
    Complex.eventually_eq_of_isLocalMax_norm hdiff_at hmax
  have hana_ψ : AnalyticOnNhd ℂ ψ (Metric.ball c r) := hψ.analyticOnNhd hopen
  have hana_c : AnalyticOnNhd ℂ (fun _ => ψ x) (Metric.ball c r) := analyticOnNhd_const
  have hpre : IsPreconnected (Metric.ball c r) :=
    (convex_ball c r).isPreconnected
  have heqOn : Set.EqOn ψ (fun _ => ψ x) (Metric.ball c r) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hana_ψ hana_c hpre hx heq
  intro z hz
  have hze := heqOn hz
  simpa [hxval] using congrArg Norm.norm hze

private theorem exists_differentiableOn_pow_eq_of_ne_zero_on_ball
    (g : ℂ → ℂ) (c : ℂ) (r : ℝ) (n : ℕ) (hn : n ≠ 0)
    (hg : DifferentiableOn ℂ g (Metric.ball c r))
    (hgz : ∀ z ∈ Metric.ball c r, g z ≠ 0) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (Metric.ball c r)
      ∧ ∀ z ∈ Metric.ball c r, ψ z ^ n = g z := by
  by_cases hr : r ≤ 0
  · refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz => ?_⟩
    have hlt : dist z c < r := Metric.mem_ball.mp hz
    have hnn : 0 ≤ dist z c := dist_nonneg
    linarith
  · push Not at hr
    have hopen : IsOpen (Metric.ball c r) := Metric.isOpen_ball
    have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
    have hana : AnalyticOnNhd ℂ g (Metric.ball c r) :=
      hg.analyticOnNhd hopen
    have hderiv : DifferentiableOn ℂ (deriv g) (Metric.ball c r) :=
      (hana.deriv_of_isOpen hopen).differentiableOn
    have hhDiff : DifferentiableOn ℂ (fun z => deriv g z / g z)
        (Metric.ball c r) :=
      hderiv.div hg hgz
    obtain ⟨L, hL⟩ := hhDiff.isExactOn_ball
    have hLdiff : DifferentiableOn ℂ L (Metric.ball c r) := by
      intro z hz
      exact ((hL z hz).differentiableAt).differentiableWithinAt
    have hGdiff : DifferentiableOn ℂ (fun z => g z * Complex.exp (-L z))
        (Metric.ball c r) :=
      hg.mul (hLdiff.neg.cexp)
    have hderiv0 : Set.EqOn
        (deriv (fun z => g z * Complex.exp (-L z))) 0
        (Metric.ball c r) := by
      intro z hz
      have hgz0 : g z ≠ 0 := hgz z hz
      have he : Complex.exp (-L z) ≠ 0 := Complex.exp_ne_zero _
      have h1 : HasDerivAt g (deriv g z) z :=
        (hg.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
      have h4 : HasDerivAt (fun w => Complex.exp (-L w))
          (Complex.exp (-L z) * (-(deriv g z / g z))) z :=
        (hL z hz).neg.cexp
      have h5 : HasDerivAt (fun w => g w * Complex.exp (-L w))
          (deriv g z * Complex.exp (-L z)
            + g z * (Complex.exp (-L z) * (-(deriv g z / g z)))) z :=
        h1.mul h4
      have hval : deriv g z * Complex.exp (-L z)
          + g z * (Complex.exp (-L z) * (-(deriv g z / g z))) = 0 := by
        field_simp
        ring
      rw [hval] at h5
      exact h5.deriv
    have hpre : IsPreconnected (Metric.ball c r) :=
      (convex_ball c r).isPreconnected
    have hconst : ∀ z ∈ Metric.ball c r,
        g z * Complex.exp (-L z) = g c * Complex.exp (-L c) := by
      intro z hz
      exact hopen.is_const_of_deriv_eq_zero hpre hGdiff hderiv0 hz hc
    have hGc : g c * Complex.exp (-L c) ≠ 0 :=
      mul_ne_zero (hgz c hc) (Complex.exp_ne_zero _)
    have hexpκ : Complex.exp (Complex.log (g c * Complex.exp (-L c)))
        = g c * Complex.exp (-L c) :=
      Complex.exp_log hGc
    have hexpL : ∀ z ∈ Metric.ball c r,
        g z
          = Complex.exp (L z + Complex.log (g c * Complex.exp (-L c))) := by
      intro z hz
      have h2 : g z * Complex.exp (-L z)
          = Complex.exp (Complex.log (g c * Complex.exp (-L c))) := by
        rw [hconst z hz]
        exact hexpκ.symm
      have he : Complex.exp (-L z) ≠ 0 := Complex.exp_ne_zero _
      have hkey : Complex.exp (L z + Complex.log (g c * Complex.exp (-L c)))
          * Complex.exp (-L z)
          = Complex.exp (Complex.log (g c * Complex.exp (-L c))) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      apply mul_right_cancel₀ he
      rw [hkey]
      exact h2
    refine ⟨fun z => Complex.exp
      ((L z + Complex.log (g c * Complex.exp (-L c))) / n), ?_, ?_⟩
    · exact ((hLdiff.add_const _).div_const (n : ℂ)).cexp
    · intro z hz
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hlog : g z
          = Complex.exp (L z + Complex.log (g c * Complex.exp (-L c))) :=
        hexpL z hz
      rw [hlog, ← Complex.exp_nat_mul]
      congr 1
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnC]

private theorem root_family_of_zero_free_sections (a : ℕ → ℂ)
    (hradius : (FormalMultilinearSeries.ofScalars Complex a).radius = 1)
    (z0 : ℂ) (hz0 : ‖z0‖ = 1) (ε : ℝ) (hε1 : ε ≤ 1)
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hzero : ∀ n : ℕ, N₀ ≤ n → ∀ w ∈ Metric.ball z0 ε,
      (∑ k ∈ Finset.range (n + 1), a k * w ^ k) ≠ 0) :
    ∃ F : ℕ → ℂ → ℂ, ∃ A : ℝ, 0 ≤ A
      ∧ (∀ k, DifferentiableOn ℂ (F k) (Metric.ball z0 ε))
      ∧ (∀ k, ∀ z ∈ Metric.ball z0 ε, F k z ^ (k + N₀)
        = ∑ j ∈ Finset.range (k + N₀ + 1), a j * z ^ j)
      ∧ (∀ k, ∀ z ∈ Metric.ball z0 ε, ‖F k z‖ ≤ A) := by
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun w => ∑ j ∈ Finset.range (k + N₀ + 1), a j * w ^ j)
      (Metric.ball z0 ε) := by
    intro k
    apply DifferentiableOn.fun_sum
    intro j _
    exact (differentiableOn_const (a j)).mul (differentiableOn_id.pow j)
  have hne : ∀ k : ℕ, ∀ w ∈ Metric.ball z0 ε,
      (fun w => ∑ j ∈ Finset.range (k + N₀ + 1), a j * w ^ j) w ≠ 0 := by
    intro k w hw
    exact hzero (k + N₀) (Nat.le_add_left N₀ k) w hw
  choose F hFdiff hFpow using fun k =>
    exists_differentiableOn_pow_eq_of_ne_zero_on_ball
      (fun w => ∑ j ∈ Finset.range (k + N₀ + 1), a j * w ^ j)
      z0 ε (k + N₀) (by omega) (hdiff k) (hne k)
  have hball2 : ∀ z ∈ Metric.ball z0 ε, ‖z‖ ≤ 2 := by
    intro z hz
    have hdist : ‖z - z0‖ < ε := by
      have h := Metric.mem_ball.mp hz
      rwa [Complex.dist_eq] at h
    calc ‖z‖ = ‖(z - z0) + z0‖ := by congr 1; abel
      _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
      _ ≤ 2 := by linarith [hz0, hε1]
  obtain ⟨C, hC1, hC⟩ := norm_section_le_of_radius a hradius.ge
  have hCnn : 0 ≤ C := zero_le_one.trans hC1
  have h4Cnn : (0:ℝ) ≤ 4 * C := mul_nonneg (by norm_num) hCnn
  refine ⟨F, 4 * C, h4Cnn, hFdiff, hFpow, ?_⟩
  intro k z hz
  have hnpos : k + N₀ ≠ 0 := by omega
  have h1le : 1 ≤ k + N₀ := by omega
  have hSk := hC (k + N₀) z (hball2 z hz)
  have hnorm : ‖F k z‖ ^ (k + N₀)
      = ‖∑ j ∈ Finset.range (k + N₀ + 1), a j * z ^ j‖ := by
    rw [← norm_pow, hFpow k z hz]
  have hCpow : C ≤ C ^ (k + N₀) := by
    have hpow1 := pow_le_pow_right₀ hC1 h1le
    simpa using hpow1
  have hpow : ‖F k z‖ ^ (k + N₀) ≤ (4 * C) ^ (k + N₀) := by
    rw [hnorm]
    calc ‖∑ j ∈ Finset.range (k + N₀ + 1), a j * z ^ j‖
        ≤ C * 4 ^ (k + N₀) := hSk
      _ = 4 ^ (k + N₀) * C := by ring
      _ ≤ 4 ^ (k + N₀) * C ^ (k + N₀) :=
          mul_le_mul_of_nonneg_left hCpow (by positivity)
      _ = (4 * C) ^ (k + N₀) := by rw [mul_pow]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h4Cnn hnpos).mp hpow

private theorem eventually_norm_le_of_normal_roots
    (z0 : ℂ) (ε : ℝ) (F : ℕ → ℂ → ℂ) (N₀ : ℕ) (A : ℝ)
    (hF : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball z0 ε))
    (hA0 : 0 ≤ A) (hA : ∀ k, ∀ z ∈ Metric.ball z0 ε, ‖F k z‖ ≤ A)
    (V : Set ℂ) (hVsub : V ⊆ Metric.ball z0 ε) (hVopen : IsOpen V)
    (c : ℂ) (hcV : c ∈ V)
    (hV : ∀ z ∈ V, ∃ m : ℝ, ∃ M : ℝ, 0 < m ∧
      ∀ᶠ k in atTop, m ≤ ‖F k z‖ ^ (k + N₀)
        ∧ ‖F k z‖ ^ (k + N₀) ≤ M) :
    ∀ q ∈ Metric.ball z0 ε, ∀ η : ℝ, 0 < η →
      ∀ᶠ k in atTop, ‖F k q‖ ≤ 1 + η := by
  intro q hq η hη
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ k in atTop, 1 + η < ‖F k q‖ :=
    hcon.mono fun k hk => not_le.mp hk
  obtain ⟨φ₁, hφ₁, hφ₁q⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hopen : IsOpen (Metric.ball z0 ε) := Metric.isOpen_ball
  have hB := NormalFamilies.isLocallyUniformlyBoundedOn_of_forall_norm_le
    hopen hA0 (fun j z hz => hA (φ₁ j) z hz)
  obtain ⟨φ₂, hφ₂, ψ, hψ, hlim⟩ := NormalFamilies.montel hopen
    (fun j => F (φ₁ j)) (fun j => hF (φ₁ j)) hB
  have hφmono : StrictMono (fun j => φ₁ (φ₂ j)) := hφ₁.comp hφ₂
  have hψV : ∀ z ∈ V, ‖ψ z‖ = 1 := by
    intro z hzV
    obtain ⟨m, M, hm, hbound⟩ := hV z hzV
    have hlimz : Filter.Tendsto (fun j => F (φ₁ (φ₂ j)) z) atTop
        (𝓝 (ψ z)) :=
      hlim.tendsto_at (hVsub hzV)
    have hnormz : Filter.Tendsto (fun j => ‖F (φ₁ (φ₂ j)) z‖) atTop
        (𝓝 ‖ψ z‖) :=
      hlimz.norm
    exact eq_one_of_pow_bounds (fun k => ‖F k z‖) (fun k => norm_nonneg _)
      N₀ (fun j => φ₁ (φ₂ j)) hφmono ‖ψ z‖ hnormz m hm M hbound
  have hcBall : c ∈ Metric.ball z0 ε := hVsub hcV
  have hev : ∀ᶠ w in 𝓝 c, ‖ψ w‖ = 1 := by
    filter_upwards [hVopen.mem_nhds hcV] with w hw using hψV w hw
  have hall := norm_eq_one_on_ball_of_norm_eq_one_near ψ z0 ε hψ c
    hcBall hev
  have hlimq : Filter.Tendsto (fun j => F (φ₁ (φ₂ j)) q) atTop
      (𝓝 (ψ q)) :=
    hlim.tendsto_at hq
  have hnormq : Filter.Tendsto (fun j => ‖F (φ₁ (φ₂ j)) q‖) atTop
      (𝓝 ‖ψ q‖) :=
    hlimq.norm
  have hψq : ‖ψ q‖ = 1 := hall q hq
  rw [hψq] at hnormq
  have hlt : ∀ᶠ j in atTop, ‖F (φ₁ (φ₂ j)) q‖ < 1 + η :=
    hnormq.eventually_lt_const (by linarith)
  have hge : ∀ᶠ j in atTop, 1 + η ≤ ‖F (φ₁ (φ₂ j)) q‖ :=
    Eventually.of_forall fun j => le_of_lt (hφ₁q (φ₂ j))
  obtain ⟨j, hj1, hj2⟩ := (hge.and hlt).exists
  linarith

/-- Jentzsch theorem on zeros of power-series sections (concept `jis_dep_a80afb88f0e7413eb0583f90`).

    Source: Dilcher-Ericksen, "Polynomials Whose Coefficients Are Stern Numbers",
    Theorem 4.3 (Jentzsch).
    Exact source URL: https://cs.uwaterloo.ca/journals/JIS/VOL24/Dilcher/dilcher51.tex
    Source lines: 381-388.
    Source text SHA-256: 92c23eed1f7e91f8e2c85193cae27e57042c1e1ebe579e2be8eeb0329726fc58.
    Source object SHA-256: 72f3e8444cd0fd6b5f55e89d6427f130b294841131d89c994fe3bb2971dbb19e.

    Truncation convention: the nth partial sum `∑ k = 0 ^ n, a k * z ^ k` is
    `PowerSeries.trunc (n + 1) (PowerSeries.mk a)`, since `trunc m` retains
    coefficients of degree strictly below `m`, so section `n` includes `a n`.

Proves `Wanted` entry `jentzsch_zeros_of_power_series_sections`.
-/
theorem jentzsch_zeros_of_power_series_sections (a : Nat -> Complex)
    (hradius : (FormalMultilinearSeries.ofScalars Complex a).radius = 1) :
    ∀ (z : Complex), ‖z‖ = 1 → ∀ (epsilon : Real), 0 < epsilon → ∀ (N : Nat),
      ∃ (n : Nat), N ≤ n ∧ ∃ (w : Complex),
        (PowerSeries.trunc (n + 1) (PowerSeries.mk a)).IsRoot w ∧ dist w z < epsilon := by
  intro z0 hz0 ε hε N
  by_contra hcon
  have hcon2 : ∀ n : ℕ, N ≤ n → ∀ w : ℂ,
      (PowerSeries.trunc (n + 1) (PowerSeries.mk a)).IsRoot w →
      ε ≤ dist w z0 := by
    intro n hn w hw
    by_contra hlt
    push Not at hlt
    exact hcon ⟨n, hn, w, hw, hlt⟩
  set ε' : ℝ := min ε 1
  have hε'0 : 0 < ε' := lt_min hε zero_lt_one
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set N₀ : ℕ := max N 1
  have hN₀N : N ≤ N₀ := Nat.le_max_left _ _
  have hN₀1 : 1 ≤ N₀ := Nat.le_max_right _ _
  have hzero : ∀ n : ℕ, N₀ ≤ n → ∀ w ∈ Metric.ball z0 ε',
      (∑ k ∈ Finset.range (n + 1), a k * w ^ k) ≠ 0 := by
    intro n hn w hw hSeq0
    have hdist : dist w z0 < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hw) hε'ε
    have hnN : N ≤ n := le_trans hN₀N hn
    have hroot : (PowerSeries.trunc (n + 1) (PowerSeries.mk a)).IsRoot w := by
      rw [Polynomial.IsRoot.def, eval_trunc_succ_mk_eq_sum]
      exact hSeq0
    have hle := hcon2 n hnN w hroot
    linarith
  obtain ⟨F, A, hA0, hFdiff, hFpow, hAbound⟩ :=
    root_family_of_zero_free_sections a hradius z0 hz0 ε' hε'1
      N₀ hN₀1 hzero
  have hUopen : IsOpen (Metric.ball z0 ε' ∩ Metric.ball 0 1) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have hw0 : ((1 - ε' / 2 : ℝ) : ℂ) * z0
      ∈ Metric.ball z0 ε' ∩ Metric.ball 0 1 := by
    have ht0 : (0:ℝ) < 1 - ε' / 2 := by linarith
    have ht1 : (1:ℝ) - ε' / 2 < 1 := by linarith
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : ((1 - ε' / 2 : ℝ) : ℂ) * z0 - z0
          = ((1 - ε' / 2 - 1 : ℝ) : ℂ) * z0 := by
        push_cast
        ring
      rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hz0, mul_one]
      have habs : |1 - ε' / 2 - 1| = ε' / 2 := by
        have h2 : (1:ℝ) - ε' / 2 - 1 = -(ε' / 2) := by ring
        rw [h2, abs_neg, abs_of_pos (by linarith)]
      rw [habs]
      linarith
    · rw [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, hz0, mul_one]
      linarith
  have hUne : (Metric.ball z0 ε' ∩ Metric.ball 0 1).Nonempty := ⟨_, hw0⟩
  have hUsub : Metric.ball z0 ε' ∩ Metric.ball 0 1 ⊆ Metric.ball 0 1 :=
    Set.inter_subset_right
  obtain ⟨c, hcU, hcne⟩ :=
    exists_sum_ne_zero_of_isOpen a hradius _ hUopen hUne hUsub
  have hVopen : IsOpen (Metric.ball z0 ε' ∩ Metric.ball 0 1
      ∩ (FormalMultilinearSeries.ofScalars Complex a).sum ⁻¹' {0}ᶜ) := by
    have hcont : ContinuousOn
        (FormalMultilinearSeries.ofScalars Complex a).sum
        (Metric.ball z0 ε' ∩ Metric.ball 0 1) :=
      (continuousOn_sum_of_radius a hradius).mono hUsub
    exact hcont.isOpen_inter_preimage hUopen isOpen_compl_singleton
  have hVsub : Metric.ball z0 ε' ∩ Metric.ball 0 1
      ∩ (FormalMultilinearSeries.ofScalars Complex a).sum ⁻¹' {0}ᶜ
      ⊆ Metric.ball z0 ε' := by
    intro z hz
    simp only [Set.mem_inter_iff] at hz
    exact hz.1.1
  have hcV : c ∈ Metric.ball z0 ε' ∩ Metric.ball 0 1
      ∩ (FormalMultilinearSeries.ofScalars Complex a).sum ⁻¹' {0}ᶜ := by
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact ⟨hcU, hcne⟩
  have hVbound : ∀ z ∈ Metric.ball z0 ε' ∩ Metric.ball 0 1
      ∩ (FormalMultilinearSeries.ofScalars Complex a).sum ⁻¹' {0}ᶜ,
      ∃ m : ℝ, ∃ M : ℝ, 0 < m ∧
        ∀ᶠ k in atTop, m ≤ ‖F k z‖ ^ (k + N₀)
          ∧ ‖F k z‖ ^ (k + N₀) ≤ M := by
    intro z hzV
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] at hzV
    obtain ⟨⟨hzB, hzBall⟩, hzne⟩ := hzV
    have hnorm : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hzBall
      rwa [Complex.dist_eq, sub_zero] at h
    have htend := tendsto_section_of_norm_lt_one a hradius z hnorm
    have hP : 0 < ‖(FormalMultilinearSeries.ofScalars Complex a).sum z‖ :=
      norm_pos_iff.mpr hzne
    have htnorm : Filter.Tendsto
        (fun n => ‖∑ k ∈ Finset.range (n + 1), a k * z ^ k‖) atTop
        (𝓝 ‖(FormalMultilinearSeries.ofScalars Complex a).sum z‖) :=
      htend.norm
    have hlo : ∀ᶠ n in atTop,
        ‖(FormalMultilinearSeries.ofScalars Complex a).sum z‖ / 2
          < ‖∑ k ∈ Finset.range (n + 1), a k * z ^ k‖ :=
      htnorm.eventually_const_lt (by linarith)
    have hhi : ∀ᶠ n in atTop,
        ‖∑ k ∈ Finset.range (n + 1), a k * z ^ k‖
          < 2 * ‖(FormalMultilinearSeries.ofScalars Complex a).sum z‖ :=
      htnorm.eventually_lt_const (by linarith)
    have hshift : Filter.Tendsto (fun k => k + N₀) atTop atTop :=
      (Filter.tendsto_add_atTop_iff_nat N₀).mpr tendsto_id
    refine ⟨‖(FormalMultilinearSeries.ofScalars Complex a).sum z‖ / 2,
      2 * ‖(FormalMultilinearSeries.ofScalars Complex a).sum z‖,
      by linarith, ?_⟩
    have h2 := hshift.eventually (hlo.and hhi)
    filter_upwards [h2] with k hk
    have hF := hFpow k z hzB
    have hnormeq : ‖F k z‖ ^ (k + N₀)
        = ‖∑ j ∈ Finset.range (k + N₀ + 1), a j * z ^ j‖ := by
      rw [← norm_pow, hF]
    rw [hnormeq]
    exact ⟨le_of_lt hk.1, le_of_lt hk.2⟩
  set q : ℂ := ((1 + ε' / 2 : ℝ) : ℂ) * z0 with hqdef
  have hnormq : ‖q‖ = 1 + ε' / 2 := by
    have hs0 : (0:ℝ) < 1 + ε' / 2 := by linarith
    rw [hqdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0, hz0, mul_one]
  have hqB : q ∈ Metric.ball z0 ε' := by
    rw [Metric.mem_ball, Complex.dist_eq, hqdef]
    have hsub : ((1 + ε' / 2 : ℝ) : ℂ) * z0 - z0
        = ((1 + ε' / 2 - 1 : ℝ) : ℂ) * z0 := by
      push_cast
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hz0, mul_one]
    have habs : |1 + ε' / 2 - 1| = ε' / 2 := by
      have h2 : (1:ℝ) + ε' / 2 - 1 = ε' / 2 := by ring
      rw [h2, abs_of_pos (by linarith)]
    rw [habs]
    linarith
  have hN9 : ∀ᶠ k in atTop, ‖F k q‖ ≤ 1 + ε' / 4 :=
    eventually_norm_le_of_normal_roots z0 ε' F N₀ A hFdiff hA0
      hAbound _ hVsub hVopen c hcV hVbound q hqB (ε' / 4) (by linarith)
  have hsec : ∀ᶠ k in atTop,
      ‖∑ j ∈ Finset.range (k + N₀ + 1), a j * q ^ j‖
        ≤ (1 + ε' / 4) ^ (k + N₀) := by
    filter_upwards [hN9] with k hk
    have hF := hFpow k q hqB
    rw [← hF, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hk _
  have hsecN : ∀ᶠ n in atTop,
      ‖∑ k ∈ Finset.range (n + 1), a k * q ^ k‖ ≤ (1 + ε' / 4) ^ n := by
    rw [Filter.eventually_atTop] at hsec ⊢
    obtain ⟨K, hK⟩ := hsec
    refine ⟨K + N₀, fun n hn => ?_⟩
    have h2 := hK (n - N₀) (by omega)
    have h3 : n - N₀ + N₀ = n := by omega
    rwa [h3] at h2
  have hηnn : (0:ℝ) ≤ ε' / 4 := by linarith
  have hltq : 1 + ε' / 4 < ‖q‖ := by
    rw [hnormq]
    linarith
  have hlt : 1 < (FormalMultilinearSeries.ofScalars Complex a).radius :=
    one_lt_radius_of_eventually_norm_section_le a q (ε' / 4) hηnn hltq hsecN
  rw [hradius] at hlt
  exact absurd hlt (lt_irrefl _)

end MathlibExt.Analysis.Complex.JentzschPowerSeriesWanted
end
