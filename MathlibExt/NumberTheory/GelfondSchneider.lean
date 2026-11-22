/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic

@[expose] public section

section

namespace MathlibExt.NumberTheory.TranscendenceWanted

/-!
# Gelfond–Schneider theorem

This file proves the Gelfond–Schneider theorem in its every-value complex form
(`gelfondSchneider_complex_exp`) and derives the real `Real.rpow` specialization
(`gelfondSchneider_real_rpow`), by Gelfond's auxiliary-function method with
Schneider–Lang minimal-order extrapolation: a Siegel-constructed exponential sum
vanishes to high order at multiples of a logarithm, a Vandermonde argument gives a
least nonvanishing order, and Jensen's formula (upper bound) contradicts the
Liouville inequality (lower bound).
-/

/-- If `b : ℂ` is not a rational cast and `L : ℕ`,
the frequency map `t ↦ i + j * b` on `Fin (L * L)` is injective, where
`(i, j)` is the unpairing of `t` via `finProdFinEquiv`.

Note: `(finProdFinEquiv.symm t).1 : Fin L` has no direct coercion to `ℂ`,
so the statement uses the `ℕ` components `(...).1.val` and `(...).2.val`
cast to `ℂ`. -/
private theorem gs_freq_injective (b : ℂ) (hb : b ∉ Set.range (algebraMap ℚ ℂ)) (L : ℕ) :
    Function.Injective (fun t : Fin (L * L) =>
      ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℂ) +
        (((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℂ) * b)) := by
  intro a c hac
  set E := (finProdFinEquiv (m := L) (n := L))
  set p := E.symm a
  set q := E.symm c
  have h : (p.1.val : ℂ) + (p.2.val : ℂ) * b
      = (q.1.val : ℂ) + (q.2.val : ℂ) * b := hac
  have key : p = q := by
    by_cases hjj : p.2.val = q.2.val
    · -- Equal second coordinates: cancel the `b` terms, compare naturals.
      have hi : (p.1.val : ℂ) = (q.1.val : ℂ) := by
        rw [hjj] at h
        linear_combination h
      have hii : p.1.val = q.1.val := Nat.cast_injective hi
      exact Prod.ext (Fin.val_injective hii) (Fin.val_injective hjj)
    · -- Distinct second coordinates: solve for `b` as a rational cast.
      have hneC : (p.2.val : ℂ) ≠ (q.2.val : ℂ) := by exact_mod_cast hjj
      have hJ : ((p.2.val : ℂ) - (q.2.val : ℂ)) ≠ 0 := sub_ne_zero.mpr hneC
      have hmul : ((p.2.val : ℂ) - (q.2.val : ℂ)) * b
          = (q.1.val : ℂ) - (p.1.val : ℂ) := by linear_combination h
      have hb_eq : b
          = ((((q.1.val : ℚ) - (p.1.val : ℚ))
              / ((p.2.val : ℚ) - (q.2.val : ℚ))) : ℂ) := by
        simp only [Rat.cast_natCast]
        rw [eq_div_iff hJ]
        linear_combination hmul
      refine absurd ?_ hb
      refine ⟨((q.1.val : ℚ) - (p.1.val : ℚ))
        / ((p.2.val : ℚ) - (q.2.val : ℚ)), ?_⟩
      simpa using hb_eq.symm
  exact E.symm.injective key

section GS_N2

variable {m : ℕ}

/-- Each summand `w ↦ u t * exp (v t * w)` is differentiable. -/
private theorem gs_summand_diff (u v : Fin m → ℂ) (t : Fin m) :
    Differentiable ℂ (fun w : ℂ => u t * Complex.exp (v t * w)) :=
  ((differentiable_id.const_mul (v t)).cexp.const_mul (u t))

/-- The exponential sum `F` is differentiable. -/
private theorem gs_expSum_diff (u v : Fin m → ℂ) :
    Differentiable ℂ (fun w : ℂ => ∑ t, u t * Complex.exp (v t * w)) := by
  apply Differentiable.fun_sum
  intro t _
  exact gs_summand_diff u v t

/-- Each summand is smooth. -/
private theorem gs_summand_contdiff (k : ℕ) (a b : ℂ) :
    ContDiff ℂ (k : ℕ∞) (fun z : ℂ => a * Complex.exp (b * z)) := by
  have hlin : ContDiff ℂ (k : ℕ∞) (fun z : ℂ => b * z) :=
    contDiff_const.mul contDiff_id
  exact contDiff_const.mul hlin.cexp

/-- Iterated derivative of a single summand. -/
private theorem gs_summand_iter (k : ℕ) (a b : ℂ) (w : ℂ) :
    iteratedDeriv k (fun z : ℂ => a * Complex.exp (b * z)) w
      = a * b ^ k * Complex.exp (b * w) := by
  have h : iteratedDeriv k (fun z : ℂ => Complex.exp (b * z)) w
      = b ^ k * Complex.exp (b * w) :=
    congrFun (iteratedDeriv_cexp_const_mul k b) w
  rw [iteratedDeriv_const_mul_field, h, mul_assoc]

/-- Iterated derivative of the exponential sum. -/
private theorem gs_iteratedDeriv_expSum (k : ℕ) (u v : Fin m → ℂ) (w : ℂ) :
    iteratedDeriv k (fun z : ℂ => ∑ t, u t * Complex.exp (v t * z)) w
      = ∑ t, u t * (v t) ^ k * Complex.exp (v t * w) := by
  trans ∑ t, iteratedDeriv k (fun z : ℂ => u t * Complex.exp (v t * z)) w
  · exact iteratedDeriv_fun_sum (f := fun (t : Fin m) (z : ℂ) => u t * Complex.exp (v t * z))
      (I := Finset.univ)
      (fun t _ => (gs_summand_contdiff k (u t) (v t)).contDiffAt)
  · exact Finset.sum_congr rfl (fun t _ => gs_summand_iter k (u t) (v t) w)

end GS_N2

/-- A nontrivial linear combination of exponentials
    sampled against distinct nodes cannot vanish at all powers below `n`. -/
private theorem gs_zero_estimate {n : ℕ} {v : Fin n → ℂ} (hv : Function.Injective v)
    {u : Fin n → ℂ} (hu : u ≠ 0) (w₀ : ℂ) :
    ∃ k : Fin n, ∑ t : Fin n, u t * v t ^ (k : ℕ) * Complex.exp (v t * w₀) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  -- Fold the exponential factor into the coefficients.
  have hsum : ∀ k : Fin n,
      ∑ j : Fin n, (u j * Complex.exp (v j * w₀)) * v j ^ (k : ℕ) = 0 := by
    intro k
    rw [← hcon k]
    apply Finset.sum_congr rfl
    intro t _
    ring
  -- Vandermonde argument: all weighted power sums vanish, so all weights vanish.
  have hu' : (fun j => u j * Complex.exp (v j * w₀)) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hv hsum
  -- Since `Complex.exp` never vanishes, `u` itself vanishes: contradiction.
  have hu0 : u = 0 := by
    funext t
    have ht : u t * Complex.exp (v t * w₀) = 0 := congrFun hu' t
    exact (mul_eq_zero.mp ht).resolve_right (Complex.exp_ne_zero _)
  exact hu hu0

section GS_AN

open scoped Topology ENNReal
open Filter

/-- Vanishing iterated derivatives pin down the analytic order. -/
private theorem gs_order_eq_of_vanish {f : ℂ → ℂ} {x : ℂ} {s : ℕ}
    (hf : AnalyticAt ℂ f x)
    (hzero : ∀ k < s, iteratedDeriv k f x = 0)
    (hne : iteratedDeriv s f x ≠ 0) :
    analyticOrderAt f x = s := by
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mpr ⟨hzero, hne⟩

/-- Power-series coefficient equals `iteratedDeriv / factorial`. -/
private theorem gs_coeff_eq_div {f : ℂ → ℂ} {x : ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {t : ℝ≥0∞}
    (hr : HasFPowerSeriesOnBall f p x t) (n : ℕ) :
    p.coeff n = iteratedDeriv n f x / (n.factorial : ℂ) := by
  have hfactC : ((n.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h1 := hr.factorial_smul (1 : ℂ) n
  rw [nsmul_eq_mul] at h1
  rw [eq_div_iff hfactC, mul_comm, iteratedDeriv_eq_iteratedFDeriv]
  exact h1

/-- The trailing coefficient is `iteratedDeriv s f x / s!`. -/
private theorem gs_trailingCoeff_eq {f : ℂ → ℂ} {x : ℂ} {s : ℕ}
    (hf : AnalyticAt ℂ f x)
    (hzero : ∀ k < s, iteratedDeriv k f x = 0)
    (hne : iteratedDeriv s f x ≠ 0) :
    meromorphicTrailingCoeffAt f x = iteratedDeriv s f x / (s.factorial : ℂ) := by
  classical
  obtain ⟨p, hp⟩ := hf
  have ⟨t, hr⟩ := hp
  have hfactC : ((s.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  have hps : p s ≠ 0 := by
    intro hcon
    apply hne
    have h0 : p.coeff s = 0 := FormalMultilinearSeries.coeff_eq_zero.mpr hcon
    rw [gs_coeff_eq_div hr s] at h0
    exact (div_eq_zero_iff.mp h0).resolve_right hfactC
  have hp0 : ∀ n < s, p n = 0 := by
    intro n hn
    rw [← FormalMultilinearSeries.coeff_eq_zero, gs_coeff_eq_div hr n,
      hzero n hn, zero_div]
  have hord : p.order = s := by
    have H : ∃ n, p n ≠ 0 := ⟨s, hps⟩
    rw [FormalMultilinearSeries.order_eq_find H]
    apply le_antisymm
    · exact Nat.find_min' H hps
    · by_contra hlt
      push Not at hlt
      exact (Nat.find_spec H) (hp0 _ hlt)
  have hfg : ∀ z : ℂ, f z = (z - x) ^ s • ((Function.swap dslope x)^[s] f) z := by
    intro z
    have h := hp.eq_pow_order_mul_iterate_dslope z
    rw [hord] at h
    exact h
  have hser : HasFPowerSeriesAt ((Function.swap dslope x)^[s] f)
      ((FormalMultilinearSeries.fslope^[s] p)) x :=
    hp.has_fpower_series_iterate_dslope_fslope s
  have hgan : AnalyticAt ℂ ((Function.swap dslope x)^[s] f) x := hser.analyticAt
  have h1 := hser.coeff_zero (1 : Fin 0 → ℂ)
  have h2 : (FormalMultilinearSeries.fslope^[s] p).coeff 0 = p.coeff (0 + s) :=
    FormalMultilinearSeries.coeff_iterate_fslope s 0
  rw [show (FormalMultilinearSeries.fslope^[s] p) 0 1
      = (FormalMultilinearSeries.fslope^[s] p).coeff 0 from rfl,
    h2, zero_add] at h1
  have hcs_ne : p.coeff s ≠ 0 := FormalMultilinearSeries.coeff_eq_zero.not.mpr hps
  have hgne : ((Function.swap dslope x)^[s] f) x ≠ 0 := by
    rw [← h1]
    exact hcs_ne
  have hev : f =ᶠ[𝓝[≠] x] fun z => (z - x) ^ (s : ℤ) • ((Function.swap dslope x)^[s] f) z := by
    filter_upwards with z
    rw [zpow_natCast]
    exact hfg z
  have htrail :=
    hgan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := (s : ℤ)) hgne hev
  rw [htrail, ← h1, gs_coeff_eq_div hr s]

/-- Divisor of an analytic function from its analytic order. -/
private theorem gs_divisor_apply_of_order {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {r : ℕ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U)
    (h : analyticOrderAt f z = (r : ℕ∞)) :
    MeromorphicOn.divisor f U z = (r : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, h, ENat.map_natCast,
    WithTop.untop₀_coe]

/-- Vanishing derivatives force a finite order `r ≥ s`. -/
private theorem gs_order_ge_of_vanish {f : ℂ → ℂ} {z : ℂ} {s : ℕ}
    (hf : AnalyticAt ℂ f z)
    (hzero : ∀ k < s, iteratedDeriv k f z = 0)
    (hne : ∃ k₀, iteratedDeriv k₀ f z ≠ 0) :
    ∃ r : ℕ, s ≤ r ∧ analyticOrderAt f z = (r : ℕ∞) := by
  classical
  obtain ⟨k₀, hk₀⟩ := hne
  have H : ∃ k, iteratedDeriv k f z ≠ 0 := ⟨k₀, hk₀⟩
  refine ⟨Nat.find H, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    exact (Nat.find_spec H) (hzero _ hlt)
  · rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf]
    refine ⟨?_, Nat.find_spec H⟩
    intro k hk
    by_contra hne'
    exact (Nat.find_min H hk) hne'

end GS_AN

section GS_JENSEN

open scoped Topology ENNReal
open Filter

/-- Jensen-type bound with an order-`s` zero at `c`. -/
private theorem gs_jensen_bound (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (s : ℕ) (B : ℝ) (hB : 1 ≤ B) (P : Finset ℂ) (hcP : c ∉ P)
    (hPR : ∀ z ∈ P, ‖z - c‖ ≤ R)
    (hzero : ∀ k < s, iteratedDeriv k F c = 0)
    (hne : iteratedDeriv s F c ≠ 0)
    (hPzero : ∀ z ∈ P, ∀ k < s, iteratedDeriv k F z = 0)
    (hPne : ∀ z ∈ P, ∃ k₀, iteratedDeriv k₀ F z ≠ 0)
    (hbound : ∀ w ∈ Metric.sphere c R, ‖F w‖ ≤ B) :
    ‖iteratedDeriv s F c‖ / (s.factorial : ℝ) * R ^ s * ∏ z ∈ P, (R / ‖c - z‖) ^ s ≤ B := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRabs : |R| = R := abs_of_pos hR
  -- (1) analytic on the closed ball, hence meromorphic
  have hA : AnalyticOnNhd ℂ F (Metric.closedBall c R) := fun z _ => hF.analyticAt z
  have hA' : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    rw [hRabs]; exact hA
  have hAsphere : AnalyticOnNhd ℂ F (Metric.sphere c |R|) := fun z _ => hF.analyticAt z
  have hM' : MeromorphicOn F (Metric.closedBall c |R|) := hA'.meromorphicOn
  have hMsphere : MeromorphicOn F (Metric.sphere c |R|) := hAsphere.meromorphicOn
  have hcmem : c ∈ Metric.closedBall c |R| := by
    rw [Metric.mem_closedBall, dist_self]
    exact abs_nonneg _
  have hcRmem : c ∈ Metric.closedBall c R := by
    rw [Metric.mem_closedBall, dist_self]
    exact hR.le
  have hAt_c : AnalyticAt ℂ F c := hA c hcRmem
  -- (3) divisor at `c` and trailing coefficient from iterated derivatives
  have hord_c : analyticOrderAt F c = s := gs_order_eq_of_vanish hAt_c hzero hne
  have hDc : MeromorphicOn.divisor F (Metric.closedBall c |R|) c = (s : ℤ) :=
    gs_divisor_apply_of_order hA' hcmem hord_c
  have htrail : meromorphicTrailingCoeffAt F c
      = iteratedDeriv s F c / (s.factorial : ℂ) :=
    gs_trailingCoeff_eq hAt_c hzero hne
  -- (2) Jensen's formula
  have hjensen := hM'.circleAverage_log_norm hRne
  -- (4) circle-average upper bound by `log B`
  have hInt : CircleIntegrable (fun x => Real.log ‖F x‖) c R :=
    hMsphere.circleIntegrable_log_norm
  have hspheq : Metric.sphere c |R| = Metric.sphere c R := by rw [hRabs]
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have hbound' : ∀ x ∈ Metric.sphere c |R|, Real.log ‖F x‖ ≤ Real.log B := by
    intro x hx
    rw [hspheq] at hx
    have hBx := hbound x hx
    rcases eq_or_ne (‖F x‖) 0 with h0 | h0
    · rw [h0, Real.log_zero]
      exact Real.log_nonneg hB
    · have hpos : 0 < ‖F x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact (Real.log_le_log_iff hpos hBpos).mpr hBx
  have hintegral : Real.circleAverage (fun x => Real.log ‖F x‖) c R ≤ Real.log B :=
    Real.circleAverage_mono_on_of_le_circle hInt hbound'
  -- facts about points of `P`
  have hPmem : ∀ z ∈ P, z ∈ Metric.closedBall c |R| := by
    intro z hz
    rw [hRabs, Metric.mem_closedBall, dist_eq_norm]
    exact hPR z hz
  have hcz : ∀ z ∈ P, c ≠ z := by
    intro z hz hcon
    exact hcP (hcon.symm ▸ hz)
  have hnorm_pos : ∀ z ∈ P, 0 < ‖c - z‖ := by
    intro z hz
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (hcz z hz)
  have hle_of_mem : ∀ u ∈ Metric.closedBall c |R|, ‖c - u‖ ≤ R := by
    intro u hu
    have hdist : dist u c ≤ |R| := Metric.mem_closedBall.mp hu
    rw [hRabs] at hdist
    rw [dist_eq_norm] at hdist
    rwa [norm_sub_rev]
  -- (5) every Jensen summand is nonnegative
  have hlog_nn : ∀ u ∈ Metric.closedBall c |R|,
      0 ≤ Real.log (R * ‖c - u‖⁻¹) := by
    intro u hu
    rcases eq_or_ne u c with rfl | hne'
    · simp
    · have hpos : 0 < ‖c - u‖ := by
        rw [norm_pos_iff]
        exact sub_ne_zero.mpr (Ne.symm hne')
      have h1 : (1 : ℝ) ≤ R * ‖c - u‖⁻¹ := by
        rw [le_mul_inv_iff₀ hpos]
        simpa using hle_of_mem u hu
      exact Real.log_nonneg h1
  have hDnn : ∀ u, (0 : ℝ)
      ≤ (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ) := by
    intro u
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA' u
  have hgnn : ∀ u, 0 ≤ (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ)
      * Real.log (R * ‖c - u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall c |R|
    · exact mul_nonneg (hDnn u) (hlog_nn u hu)
    · have h0 : MeromorphicOn.divisor F (Metric.closedBall c |R|) u = 0 := by
        by_contra hne'
        exact hu ((MeromorphicOn.divisor F (Metric.closedBall c |R|)).supportWithinDomain
          (Function.mem_support.mpr hne'))
      rw [h0]
      simp
  -- (6) divisor at `z ∈ P` is at least `s`
  have hDz : ∀ z ∈ P, (s : ℝ)
      ≤ (MeromorphicOn.divisor F (Metric.closedBall c |R|) z : ℝ) := by
    intro z hz
    obtain ⟨r, hsr, hr⟩ :=
      gs_order_ge_of_vanish (hA' z (hPmem z hz)) (hPzero z hz) (hPne z hz)
    have hDv : MeromorphicOn.divisor F (Metric.closedBall c |R|) z = (r : ℤ) :=
      gs_divisor_apply_of_order hA' (hPmem z hz) hr
    rw [hDv]
    exact_mod_cast hsr
  have hPbound : ∀ z ∈ P, (s : ℝ) * Real.log (R * ‖c - z‖⁻¹)
      ≤ (MeromorphicOn.divisor F (Metric.closedBall c |R|) z : ℝ)
        * Real.log (R * ‖c - z‖⁻¹) := by
    intro z hz
    exact mul_le_mul_of_nonneg_right (hDz z hz) (hlog_nn z (hPmem z hz))
  -- finsum lower bound over the finite set `hg.toFinset ∪ P`
  have hsuppD : (MeromorphicOn.divisor F (Metric.closedBall c |R|)).support.Finite :=
    (MeromorphicOn.divisor F (Metric.closedBall c |R|)).finiteSupport
      (isCompact_closedBall _ _)
  have hg : (fun u => (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ)
      * Real.log (R * ‖c - u‖⁻¹)).HasFiniteSupport := by
    apply hsuppD.subset
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hcon
    apply hu
    rw [hcon]
    simp
  have hG : (∑ᶠ u, (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ)
        * Real.log (R * ‖c - u‖⁻¹))
      = ∑ u ∈ hg.toFinset ∪ P, (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ)
        * Real.log (R * ‖c - u‖⁻¹) := by
    rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ∪ P)]
    intro u hu
    apply Finset.mem_coe.mpr
    exact Finset.mem_union_left P (hg.mem_toFinset.mpr hu)
  have hPlower : (∑ z ∈ P, (s : ℝ) * Real.log (R * ‖c - z‖⁻¹))
      ≤ ∑ u ∈ hg.toFinset ∪ P, (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ)
        * Real.log (R * ‖c - u‖⁻¹) := by
    calc (∑ z ∈ P, (s : ℝ) * Real.log (R * ‖c - z‖⁻¹))
        ≤ ∑ z ∈ P, (MeromorphicOn.divisor F (Metric.closedBall c |R|) z : ℝ)
            * Real.log (R * ‖c - z‖⁻¹) :=
          Finset.sum_le_sum (fun i hi => hPbound i hi)
      _ ≤ ∑ u ∈ hg.toFinset ∪ P, (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ)
            * Real.log (R * ‖c - u‖⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          intro i _ hni
          exact hgnn i
  have hle : (∑ z ∈ P, (s : ℝ) * Real.log (R * ‖c - z‖⁻¹))
      ≤ (∑ᶠ u, (MeromorphicOn.divisor F (Metric.closedBall c |R|) u : ℝ)
        * Real.log (R * ‖c - u‖⁻¹)) := by
    rw [hG]; exact hPlower
  have hcast : (((s : ℤ)) : ℝ) = (s : ℝ) := Int.cast_natCast s
  rw [hDc, htrail, hcast] at hjensen
  have hcomb : Real.log ‖iteratedDeriv s F c / (s.factorial : ℂ)‖ + (s : ℝ) * Real.log R
      + (∑ z ∈ P, (s : ℝ) * Real.log (R * ‖c - z‖⁻¹)) ≤ Real.log B := by
    linarith
  -- (7) fold into one log and conclude by monotonicity
  have hfact_pos : (0 : ℝ) < (s.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos s
  have hfact_ne : (s.factorial : ℝ) ≠ 0 := ne_of_gt hfact_pos
  have hdnorm : ‖iteratedDeriv s F c‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hTpos : (0 : ℝ) < ‖iteratedDeriv s F c‖ / (s.factorial : ℝ) :=
    div_pos (norm_pos_iff.mpr hne) hfact_pos
  have hRpow : (0 : ℝ) < R ^ s := pow_pos hR s
  have hprod_pos : (0 : ℝ) < ∏ z ∈ P, (R / ‖c - z‖) ^ s := by
    apply Finset.prod_pos
    intro z hz
    exact pow_pos (div_pos hR (hnorm_pos z hz)) s
  have hLHSpos : (0 : ℝ) < ‖iteratedDeriv s F c‖ / (s.factorial : ℝ) * R ^ s
      * ∏ z ∈ P, (R / ‖c - z‖) ^ s :=
    mul_pos (mul_pos hTpos hRpow) hprod_pos
  apply (Real.log_le_log_iff hLHSpos hBpos).mp
  have hnormtrail : ‖iteratedDeriv s F c / (s.factorial : ℂ)‖
      = ‖iteratedDeriv s F c‖ / (s.factorial : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
  have e1 : Real.log (‖iteratedDeriv s F c‖ / (s.factorial : ℝ) * R ^ s)
      = Real.log ‖iteratedDeriv s F c‖ - Real.log (s.factorial : ℝ)
        + (s : ℝ) * Real.log R := by
    rw [Real.log_mul (div_ne_zero hdnorm hfact_ne) (pow_ne_zero s hRne),
      Real.log_div hdnorm hfact_ne, Real.log_pow]
  have e2 : Real.log (∏ z ∈ P, (R / ‖c - z‖) ^ s)
      = ∑ z ∈ P, (s : ℝ) * Real.log (R * ‖c - z‖⁻¹) := by
    rw [Real.log_prod (fun z hz => pow_ne_zero s
      (div_ne_zero hRne (ne_of_gt (hnorm_pos z hz))))]
    apply Finset.sum_congr rfl
    intro z _
    rw [Real.log_pow, div_eq_mul_inv]
  have e3 : Real.log ‖iteratedDeriv s F c / (s.factorial : ℂ)‖
      = Real.log ‖iteratedDeriv s F c‖ - Real.log (s.factorial : ℝ) := by
    rw [hnormtrail, Real.log_div hdnorm hfact_ne]
  rw [Real.log_mul (mul_ne_zero (div_ne_zero hdnorm hfact_ne) (pow_ne_zero s hRne))
    (Finset.prod_ne_zero_iff.mpr (fun z hz => pow_ne_zero s
      (div_ne_zero hRne (ne_of_gt (hnorm_pos z hz))))), e1, e2, ← e3]
  exact hcomb

end GS_JENSEN

section GS_NF

open scoped NumberField

/-- Siegel-type existence: uniform constant `C₀` giving a small nonzero integral
solution of an underdetermined linear system over `𝓞 K`, with house bounds. -/
private theorem gs_siegel_exist (K : Type*) [Field K] [NumberField K] :
    ∃ C₀ : ℝ, ∀ (α β : Type*) [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)),
      a ≠ 0 → ∀ (p q : ℕ), 0 < p → p < q → Fintype.card β = q → ∀ (A : ℝ),
        (∀ k l, NumberField.house (algebraMap (𝓞 K) K (a k l)) ≤ A) →
          Fintype.card α = p →
          ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a.mulVec ξ = 0 ∧
            ∀ l, NumberField.house ((ξ l) : K) ≤
              C₀ * (C₀ * q * A) ^ ((p : ℝ) / (q - p)) := by
  classical
  refine ⟨?w, ?_⟩
  swap
  · intro α β hα hβ a ha p q h0p hpq cardβ A habs cardα
    exact NumberField.house.exists_ne_zero_int_vec_house_le K a ha h0p hpq cardβ habs cardα

/-- Liouville-type lower bound: a nonzero algebraic integer cannot be too small
at one embedding relative to its house. -/
private theorem gs_liouville (K : Type*) [Field K] [NumberField K] (σ : K →+* ℂ)
    (Γ : 𝓞 K) (hΓ : Γ ≠ 0) (Y : ℝ)
    (hY : NumberField.house ((Γ : 𝓞 K) : K) ≤ Y) :
    1 ≤ ‖σ ((Γ : 𝓞 K) : K)‖ * Y ^ (Module.finrank ℚ K - 1) := by
  have hN : Algebra.norm ℤ Γ ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (NumberField.RingOfIntegers.basis K)).mpr hΓ
  have h1 : (1 : ℝ) ≤ ‖Algebra.norm ℚ ((Γ : 𝓞 K) : K)‖ := by
    rw [← Algebra.coe_norm_int, Int.norm_cast_rat, Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hN
  have hmain := NumberField.norm_norm_le_norm_mul_house_pow ((Γ : 𝓞 K) : K) σ
  have hpow : NumberField.house ((Γ : 𝓞 K) : K) ^ (Module.finrank ℚ K - 1) ≤
      Y ^ (Module.finrank ℚ K - 1) :=
    pow_le_pow_left₀ (NumberField.house_nonneg _) hY _
  calc (1 : ℝ) ≤ ‖Algebra.norm ℚ ((Γ : 𝓞 K) : K)‖ := h1
    _ ≤ ‖σ ((Γ : 𝓞 K) : K)‖ * NumberField.house ((Γ : 𝓞 K) : K) ^ (Module.finrank ℚ K - 1) :=
        hmain
    _ ≤ ‖σ ((Γ : 𝓞 K) : K)‖ * Y ^ (Module.finrank ℚ K - 1) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)

end GS_NF

section GS_SETUP

open scoped NumberField

-- The generators lie in the adjoined field.
private theorem gs_mem_adjoin_a (a b c : ℂ) :
    a ∈ IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ) :=
  IntermediateField.subset_adjoin ℚ ({a, b, c} : Set ℂ) (by simp)

private theorem gs_mem_adjoin_b (a b c : ℂ) :
    b ∈ IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ) :=
  IntermediateField.subset_adjoin ℚ ({a, b, c} : Set ℂ) (by simp)

private theorem gs_mem_adjoin_c (a b c : ℂ) :
    c ∈ IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ) :=
  IntermediateField.subset_adjoin ℚ ({a, b, c} : Set ℂ) (by simp)

-- Finite-dimensionality over ℚ.
private theorem gs_finiteDimensional (a b c : ℂ) (ha : IsAlgebraic ℚ a)
    (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) := by
  have hfin : ({a, b, c} : Set ℂ).Finite := by
    rw [Set.finite_insert, Set.finite_insert]
    exact Set.finite_singleton c
  have : Fintype ({a, b, c} : Set ℂ) := hfin.fintype
  have : Finite ({a, b, c} : Set ℂ) := Finite.of_fintype _
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact isAlgebraic_iff_isIntegral.mp ha
  · exact isAlgebraic_iff_isIntegral.mp hb
  · exact isAlgebraic_iff_isIntegral.mp hc

-- Characteristic zero via the embedding into ℂ.
private theorem gs_charZero (a b c : ℂ) :
    CharZero (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) := by
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℚ _)

-- The adjoined field is a number field.
private theorem gs_numberField (a b c : ℂ) (ha : IsAlgebraic ℚ a)
    (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c) :
    NumberField (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) where
  to_charZero := gs_charZero a b c
  to_finiteDimensional := gs_finiteDimensional a b c ha hb hc

-- The degree is at least one.
private theorem gs_finrank_pos (a b c : ℂ) (ha : IsAlgebraic ℚ a)
    (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c) :
    0 < Module.finrank ℚ (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) := by
  have hFin : Module.Finite ℚ
      (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) :=
    @NumberField.to_finiteDimensional _ _
      (gs_numberField a b c ha hb hc)
  exact @Module.finrank_pos ℚ _ _ _ _ _ hFin _ _ _

end GS_SETUP

section GS_DENOM

open scoped NumberField

-- Simultaneous clearing of denominators.
private theorem gs_clear_denominators (a b c : ℂ) (ha : IsAlgebraic ℚ a)
    (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c) :
    ∃ δ : ℕ, 0 < δ ∧
      ∃ α' β' γ' : 𝓞 (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)),
        (α' : IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) =
          δ • (⟨a, gs_mem_adjoin_a a b c⟩ :
            IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) ∧
        (β' : IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) =
          δ • (⟨b, gs_mem_adjoin_b a b c⟩ :
            IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) ∧
        (γ' : IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) =
          δ • (⟨c, gs_mem_adjoin_c a b c⟩ :
            IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) := by
  have haQ : IsIntegral ℚ a := isAlgebraic_iff_isIntegral.mp ha
  have hbQ : IsIntegral ℚ b := isAlgebraic_iff_isIntegral.mp hb
  have hcQ : IsIntegral ℚ c := isAlgebraic_iff_isIntegral.mp hc
  obtain ⟨m₁, h₁⟩ :=
    haQ.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) _
  obtain ⟨m₂, h₂⟩ :=
    hbQ.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) _
  obtain ⟨m₃, h₃⟩ :=
    hcQ.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) _
  set δ₀ : ℤ := (m₁ : ℤ) * (m₂ : ℤ) * (m₃ : ℤ) with hδ₀
  have hm₁ : (m₁ : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp m₁.2
  have hm₂ : (m₂ : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp m₂.2
  have hm₃ : (m₃ : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp m₃.2
  have hδ₀ne : δ₀ ≠ 0 := by
    rw [hδ₀]
    exact mul_ne_zero (mul_ne_zero hm₁ hm₂) hm₃
  have hda : IsIntegral ℤ (δ₀ • a) := by
    have hmod : δ₀ = ((m₂ : ℤ) * (m₃ : ℤ)) * (m₁ : ℤ) := by rw [hδ₀]; ring
    rw [hmod, mul_smul]
    exact h₁.smul _
  have hdb : IsIntegral ℤ (δ₀ • b) := by
    have hmod : δ₀ = ((m₁ : ℤ) * (m₃ : ℤ)) * (m₂ : ℤ) := by rw [hδ₀]; ring
    rw [hmod, mul_smul]
    exact h₂.smul _
  have hdc : IsIntegral ℤ (δ₀ • c) := by
    have hmod : δ₀ = ((m₁ : ℤ) * (m₂ : ℤ)) * (m₃ : ℤ) := hδ₀
    rw [hmod, mul_smul]
    exact h₃.smul _
  have hδpos : 0 < δ₀.natAbs := by
    rw [Nat.pos_iff_ne_zero]
    intro hz
    apply hδ₀ne
    obtain h | h := Int.natAbs_eq δ₀
    · rw [h, hz, Nat.cast_zero]
    · rw [h, hz, Nat.cast_zero, neg_zero]
  have hN : ((((δ₀.natAbs : ℕ))) : ℤ) = δ₀ ∨
      ((((δ₀.natAbs : ℕ))) : ℤ) = -δ₀ := by
    obtain h | h := Int.natAbs_eq δ₀
    · exact Or.inl h.symm
    · refine Or.inr ?_
      conv_rhs => rw [h]
      rw [neg_neg]
  have hsmul : ∀ x : ℂ, (δ₀.natAbs : ℕ) • x = (((δ₀.natAbs : ℕ) : ℤ)) • x := by
    intro x
    rw [nsmul_eq_mul]
    simp only [Algebra.smul_def, map_natCast]
  have hca : IsIntegral ℤ ((δ₀.natAbs : ℕ) • a) := by
    rw [hsmul]
    obtain h | h := hN
    · rw [h]; exact hda
    · rw [h, neg_smul]; exact hda.neg
  have hcb : IsIntegral ℤ ((δ₀.natAbs : ℕ) • b) := by
    rw [hsmul]
    obtain h | h := hN
    · rw [h]; exact hdb
    · rw [h, neg_smul]; exact hdb.neg
  have hcc : IsIntegral ℤ ((δ₀.natAbs : ℕ) • c) := by
    rw [hsmul]
    obtain h | h := hN
    · rw [h]; exact hdc
    · rw [h, neg_smul]; exact hdc.neg
  have hfinj : Function.Injective
      (((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ)) :=
    Subtype.val_injective
  have hKa : IsIntegral ℤ ((δ₀.natAbs : ℕ) •
      (⟨a, gs_mem_adjoin_a a b c⟩ :
        IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))) := by
    have hmap : (((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
        ((δ₀.natAbs : ℕ) • (⟨a, gs_mem_adjoin_a a b c⟩ :
          IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))) =
        (δ₀.natAbs : ℕ) • a := by
      have e : (((IntermediateField.val
          (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
          (⟨a, gs_mem_adjoin_a a b c⟩ :
            IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) = a := rfl
      rw [map_nsmul, e]
    have hccK : IsIntegral ℤ ((((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
        ((δ₀.natAbs : ℕ) • (⟨a, gs_mem_adjoin_a a b c⟩ :
          IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)))) := by
      rw [hmap]; exact hca
    exact (isIntegral_algHom_iff
      (((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
      hfinj).mp hccK
  have hKb : IsIntegral ℤ ((δ₀.natAbs : ℕ) •
      (⟨b, gs_mem_adjoin_b a b c⟩ :
        IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))) := by
    have hmap : (((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
        ((δ₀.natAbs : ℕ) • (⟨b, gs_mem_adjoin_b a b c⟩ :
          IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))) =
        (δ₀.natAbs : ℕ) • b := by
      have e : (((IntermediateField.val
          (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
          (⟨b, gs_mem_adjoin_b a b c⟩ :
            IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) = b := rfl
      rw [map_nsmul, e]
    have hccK : IsIntegral ℤ ((((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
        ((δ₀.natAbs : ℕ) • (⟨b, gs_mem_adjoin_b a b c⟩ :
          IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)))) := by
      rw [hmap]; exact hcb
    exact (isIntegral_algHom_iff
      (((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
      hfinj).mp hccK
  have hKc : IsIntegral ℤ ((δ₀.natAbs : ℕ) •
      (⟨c, gs_mem_adjoin_c a b c⟩ :
        IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))) := by
    have hmap : (((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
        ((δ₀.natAbs : ℕ) • (⟨c, gs_mem_adjoin_c a b c⟩ :
          IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))) =
        (δ₀.natAbs : ℕ) • c := by
      have e : (((IntermediateField.val
          (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
          (⟨c, gs_mem_adjoin_c a b c⟩ :
            IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)) = c := rfl
      rw [map_nsmul, e]
    have hccK : IsIntegral ℤ ((((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
        ((δ₀.natAbs : ℕ) • (⟨c, gs_mem_adjoin_c a b c⟩ :
          IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)))) := by
      rw [hmap]; exact hcc
    exact (isIntegral_algHom_iff
      (((IntermediateField.val
        (IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ))).restrictScalars ℤ))
      hfinj).mp hccK
  refine ⟨δ₀.natAbs, hδpos,
    ⟨(δ₀.natAbs : ℕ) • (⟨a, gs_mem_adjoin_a a b c⟩ :
      IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)),
      (mem_integralClosure_iff ℤ _).mpr hKa⟩,
    ⟨(δ₀.natAbs : ℕ) • (⟨b, gs_mem_adjoin_b a b c⟩ :
      IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)),
      (mem_integralClosure_iff ℤ _).mpr hKb⟩,
    ⟨(δ₀.natAbs : ℕ) • (⟨c, gs_mem_adjoin_c a b c⟩ :
      IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)),
      (mem_integralClosure_iff ℤ _).mpr hKc⟩, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

end GS_DENOM

section GS_NF2

open scoped NumberField

-- Values of the auxiliary exponential function.
private theorem gs_exp_values {ℓ a b c : ℂ} (h1 : Complex.exp ℓ = a)
    (h2 : Complex.exp (b * ℓ) = c) (i j n : ℕ) :
    Complex.exp (((i : ℂ) + (j : ℂ) * b) * ((n : ℂ) * ℓ)) =
      a ^ (i * n) * c ^ (j * n) := by
  have harg : ((i : ℂ) + (j : ℂ) * b) * ((n : ℂ) * ℓ)
      = ((i * n : ℕ) : ℂ) * ℓ + ((j * n : ℕ) : ℂ) * (b * ℓ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul, h1, h2]

end GS_NF2

section GS_DEFS

open scoped NumberField

/-- Frequency at column `t : Fin (L * L)` (same formula as in `gs_freq_injective`). -/
private def gs_ω (b : ℂ) (L : ℕ) (t : Fin (L * L)) : ℂ :=
  ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℂ) +
    (((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℂ) * b)

/-- Frequency at column `t`, as an element of `K`. -/
private def gs_ωK (K : Type*) [Field K] (L : ℕ) (bK : K) (t : Fin (L * L)) : K :=
  ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : K) +
    (((finProdFinEquiv (m := L) (n := L)).symm t).2.val : K) * bK)

/-- Auxiliary ring-of-integers matrix entry. -/
private def gs_e (K : Type*) [Field K] [NumberField K] (δ L : ℕ)
    (α' β' γ' : 𝓞 K) (E' k n : ℕ) (t : Fin (L * L)) : 𝓞 K :=
  (δ : 𝓞 K) ^ (E' - k - ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
      ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
    (((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : 𝓞 K)) * (δ : 𝓞 K) +
      ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : 𝓞 K)) * β') ^ k *
    α' ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
    γ' ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)

/-- The matrix entry maps to `δ ^ E'` times the
exponential-sum term, in `K` and in `ℂ`, and satisfies the house bound. -/
private theorem gs_entry (K : Type*) [Field K] [NumberField K] (ι : K →+* ℂ)
    {δ L E' k n : ℕ} {H : ℝ} {a b c : ℂ} {aK bK cK : K}
    {α' β' γ' : 𝓞 K} {t : Fin (L * L)}
    (haK : ι aK = a) (hbK : ι bK = b) (hcK : ι cK = c)
    (hα : (α' : K) = δ • aK) (hβ : (β' : K) = δ • bK) (hγ : (γ' : K) = δ • cK)
    (hle : k + ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n +
      ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n ≤ E')
    (hH : 1 ≤ H) (hδH : (δ : ℝ) ≤ H)
    (hHα : NumberField.house (α' : K) ≤ H)
    (hHβ : NumberField.house (β' : K) ≤ H)
    (hHγ : NumberField.house (γ' : K) ≤ H) :
    algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' k n t)
        = (δ : K) ^ E' * ((gs_ωK K L bK t) ^ k *
          aK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          cK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
      ∧ ι (algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' k n t))
        = (δ : ℂ) ^ E' * ((gs_ω b L t) ^ k *
          a ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          c ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
      ∧ NumberField.house (algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' k n t))
        ≤ H ^ E' * (2 * (L : ℝ)) ^ k := by
  have hexp : (E' - k - ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
      ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) + k +
      (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) +
      (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) = E' := by
    omega
  have e_δ : algebraMap (𝓞 K) K ((δ : 𝓞 K) ^ (E' - k -
      ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
      ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
      = (δ : K) ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) := by
    rw [map_pow, map_natCast]
  have e_mid : algebraMap (𝓞 K) K
      (((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : 𝓞 K)) * (δ : 𝓞 K) +
        ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : 𝓞 K)) * β')
      = (δ : K) * gs_ωK K L bK t := by
    simp only [map_add, map_mul, map_natCast,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [hβ, nsmul_eq_mul]
    unfold gs_ωK
    ring
  have e_α : algebraMap (𝓞 K) K
      (α' ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n))
      = (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
        aK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) := by
    rw [map_pow]
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [hα, nsmul_eq_mul, mul_pow]
  have e_γ : algebraMap (𝓞 K) K
      (γ' ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
      = (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
        cK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) := by
    rw [map_pow]
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [hγ, nsmul_eq_mul, mul_pow]
  have hK : algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' k n t)
      = (δ : K) ^ E' * ((gs_ωK K L bK t) ^ k *
        aK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
        cK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) := by
    have step : algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' k n t)
        = (((δ : K) ^ (E' - k -
            ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
            ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
          (δ : K) ^ k *
          (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) *
          ((gs_ωK K L bK t) ^ k *
            aK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
            cK ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))) := by
      unfold gs_e
      rw [map_mul, map_mul, map_mul, e_δ, e_α, e_γ, map_pow, e_mid, mul_pow]
      ring
    have hHpow : ((δ : K) ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
      (δ : K) ^ k *
      (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
      (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) =
        (δ : K) ^ E' := by
      calc ((δ : K) ^ (E' - k -
            ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
            ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
          (δ : K) ^ k *
          (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          (δ : K) ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
          = (δ : K) ^ ((E' - k -
            ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
            ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) + k +
            (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) +
            (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) := by
            rw [← pow_add, ← pow_add, ← pow_add]
        _ = (δ : K) ^ E' := by rw [hexp]
    rw [step, hHpow]
  have hω : ι (gs_ωK K L bK t) = gs_ω b L t := by
    unfold gs_ωK gs_ω
    simp only [map_add, map_mul, map_natCast]
    rw [hbK]
  have hC : ι (algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' k n t))
      = (δ : ℂ) ^ E' * ((gs_ω b L t) ^ k *
        a ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
        c ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) := by
    rw [hK, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
      map_natCast, hω, haK, hcK]
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hnat_coe : ∀ r : ℕ, NumberField.house (((r : 𝓞 K)) : K) = (r : ℝ) := by
    intro r
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, ← Int.cast_natCast,
      map_intCast, NumberField.house_intCast, Int.cast_abs, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg r)]
  have hnat : ∀ r : ℕ,
      NumberField.house (algebraMap (𝓞 K) K ((r : 𝓞 K))) = (r : ℝ) := by
    intro r
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact hnat_coe r
  have hαh : NumberField.house (algebraMap (𝓞 K) K α') ≤ H := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]; exact hHα
  have hβh : NumberField.house (algebraMap (𝓞 K) K β') ≤ H := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]; exact hHβ
  have hγh : NumberField.house (algebraMap (𝓞 K) K γ') ≤ H := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]; exact hHγ
  have hiR : ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℝ)) ≤ (L : ℝ) := by
    exact_mod_cast Nat.le_of_lt (Fin.is_lt _)
  have hjR : ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℝ)) ≤ (L : ℝ) := by
    exact_mod_cast Nat.le_of_lt (Fin.is_lt _)
  have h1 : NumberField.house (algebraMap (𝓞 K) K
      (((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : 𝓞 K)) * (δ : 𝓞 K)))
      ≤ (L : ℝ) * H := by
    rw [map_mul]
    refine (NumberField.house_mul_le _ _).trans ?_
    rw [hnat, hnat]
    exact mul_le_mul hiR hδH (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h2 : NumberField.house (algebraMap (𝓞 K) K
      (((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : 𝓞 K)) * β'))
      ≤ (L : ℝ) * H := by
    rw [map_mul]
    refine (NumberField.house_mul_le _ _).trans ?_
    rw [hnat]
    exact mul_le_mul hjR hβh (NumberField.house_nonneg _) (Nat.cast_nonneg _)
  have hmid : NumberField.house (algebraMap (𝓞 K) K
      (((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : 𝓞 K)) * (δ : 𝓞 K) +
        ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : 𝓞 K)) * β'))
      ≤ 2 * (L : ℝ) * H := by
    rw [map_add]
    refine (NumberField.house_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    have heq : (L : ℝ) * H + (L : ℝ) * H = 2 * (L : ℝ) * H := by ring
    rw [heq]
  have hA : NumberField.house ((algebraMap (𝓞 K) K (δ : 𝓞 K)) ^ (E' - k -
      ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
      ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
      ≤ H ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) := by
    rw [NumberField.house_pow, hnat]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hδH _
  have hB : NumberField.house (algebraMap (𝓞 K) K
      (((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : 𝓞 K)) * (δ : 𝓞 K) +
        ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : 𝓞 K)) * β') ^ k)
      ≤ (2 * (L : ℝ) * H) ^ k := by
    rw [NumberField.house_pow]
    exact pow_le_pow_left₀ (NumberField.house_nonneg _) hmid _
  have hCα : NumberField.house ((algebraMap (𝓞 K) K α') ^
      (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n))
      ≤ H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) := by
    rw [NumberField.house_pow]
    exact pow_le_pow_left₀ (NumberField.house_nonneg _) hαh _
  have hDγ : NumberField.house ((algebraMap (𝓞 K) K γ') ^
      (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
      ≤ H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) := by
    rw [NumberField.house_pow]
    exact pow_le_pow_left₀ (NumberField.house_nonneg _) hγh _
  have hfin2 : (H ^ (E' - k -
      ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
      ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
      (2 * (L : ℝ) * H) ^ k) *
      (H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
        H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
      = H ^ E' * (2 * (L : ℝ)) ^ k := by
    have e : (H ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
        (2 * (L : ℝ) * H) ^ k) *
        (H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
        = (H ^ (E' - k -
          ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
          ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
          H ^ k *
          H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) *
          (2 * (L : ℝ)) ^ k := by
      rw [mul_pow]; ring
    have hHpow : (H ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
        H ^ k *
        H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
        H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) =
          H ^ E' := by
      calc (H ^ (E' - k -
              ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
              ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
            H ^ k *
            H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
            H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n))
            = H ^ ((E' - k -
              ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
              ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) + k +
              (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) +
              (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) := by
              rw [← pow_add, ← pow_add, ← pow_add]
          _ = H ^ E' := by rw [hexp]
    rw [e, hHpow]
  refine ⟨hK, hC, ?_⟩
  unfold gs_e
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, mul_assoc]
  refine (NumberField.house_mul_le _ _).trans ?_
  refine (mul_le_mul (NumberField.house_mul_le _ _) (NumberField.house_mul_le _ _)
    (NumberField.house_nonneg _) (mul_nonneg (NumberField.house_nonneg _)
      (NumberField.house_nonneg _))).trans ?_
  have hABCD : (NumberField.house ((algebraMap (𝓞 K) K (δ : 𝓞 K)) ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) *
      NumberField.house (algebraMap (𝓞 K) K
        (((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : 𝓞 K)) * (δ : 𝓞 K) +
          ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : 𝓞 K)) * β') ^ k)) *
      (NumberField.house ((algebraMap (𝓞 K) K α') ^
        (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n)) *
      NumberField.house ((algebraMap (𝓞 K) K γ') ^
        (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)))
      ≤ (H ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
        (2 * (L : ℝ) * H) ^ k) *
        (H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)) := by
    have hnn2LH : (0 : ℝ) ≤ 2 * (L : ℝ) * H :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hH0
    have hnnB : (0 : ℝ) ≤ (2 * (L : ℝ) * H) ^ k := pow_nonneg hnn2LH _
    have hnnC : (0 : ℝ) ≤ H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) :=
      pow_nonneg hH0 _
    have hnnD : (0 : ℝ) ≤ H ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) :=
      pow_nonneg hH0 _
    have hnnE0 : (0 : ℝ) ≤ H ^ (E' - k -
        ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) :=
      pow_nonneg hH0 _
    have hAB := mul_le_mul hA hB (NumberField.house_nonneg _) hnnE0
    have hCD := mul_le_mul hCα hDγ (NumberField.house_nonneg _) hnnC
    exact mul_le_mul hAB hCD (mul_nonneg (NumberField.house_nonneg _)
      (NumberField.house_nonneg _)) (mul_nonneg hnnE0 hnnB)
  exact hABCD.trans hfin2.le

/-- Siegel construction of the auxiliary exponential sum
with vanishing derivatives at the sample points. -/
private theorem gs_aux_function (K : Type*) [Field K] [NumberField K]
    {a b c ℓ : ℂ} {δ L M m E : ℕ} {H A X : ℝ}
    {ι : K →+* ℂ} {aK bK cK : K} {α' β' γ' : 𝓞 K}
    (haK : ι aK = a) (hbK : ι bK = b) (hcK : ι cK = c)
    (hℓa : Complex.exp ℓ = a) (hℓc : Complex.exp (b * ℓ) = c)
    (hα : (α' : K) = δ • aK) (hβ : (β' : K) = δ • bK) (hγ : (γ' : K) = δ • cK)
    (h1δ : 1 ≤ δ) (C₀ : ℝ) (hC₂ : C₀ ^ 2 ≤ H)
    (hC₀ : ∀ (α β : Type) [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)),
      a ≠ 0 → ∀ (p q : ℕ), 0 < p → p < q → Fintype.card β = q → ∀ (A : ℝ),
        (∀ k l, NumberField.house (algebraMap (𝓞 K) K (a k l)) ≤ A) →
          Fintype.card α = p →
          ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a.mulVec ξ = 0 ∧
            ∀ l, NumberField.house ((ξ l) : K) ≤
              C₀ * (C₀ * q * A) ^ ((p : ℝ) / (q - p)))
    (hH : 1 ≤ H) (hδH : (δ : ℝ) ≤ H)
    (hHα : NumberField.house (α' : K) ≤ H)
    (hHβ : NumberField.house (β' : K) ≤ H)
    (hHγ : NumberField.house (γ' : K) ≤ H)
    (h1L : 1 ≤ L) (h1m : 1 ≤ m) (h1M : 1 ≤ M)
    (hE : ∀ (k n : ℕ) (t : Fin (L * L)), k < M → n ≤ m →
      k + ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n +
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n ≤ E)
    (hA : A = H ^ E * (2 * (L : ℝ)) ^ M) (hX : X = H * (L : ℝ) ^ 2 * A)
    (hq : L * L = 2 * (M * m)) (hp : 0 < M * m) :
    ∃ ξ : Fin (L * L) → 𝓞 K, ξ ≠ 0 ∧ (∀ t, NumberField.house ((ξ t) : K) ≤ X) ∧
      ∀ (k n : ℕ), k < M → 1 ≤ n → n ≤ m →
        iteratedDeriv k (fun w : ℂ => ∑ t, ι ((ξ t) : K) * Complex.exp (gs_ω b L t * w))
          ((n : ℂ) * ℓ) = 0 := by
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hδK : ((δ : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt h1δ)
  have hδC : ((δ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt h1δ)
  have hL0 : 0 < L := h1L
  have hM0 : 0 < M := h1M
  have hm0 : 0 < m := h1m
  -- The Siegel matrix is nonzero: entry `(0, 0), t₀` maps to `δ ^ E ≠ 0` in `K`.
  have hΦne : (fun p : Fin M × Fin m => fun t : Fin (L * L) =>
      gs_e K δ L α' β' γ' E p.1.val (p.2.val + 1) t) ≠ 0 := by
    intro hcon
    have hLL : 0 < L * L := Nat.mul_pos hL0 hL0
    set t₀ : Fin (L * L) :=
      (finProdFinEquiv (m := L) (n := L)) (⟨0, hL0⟩, ⟨0, hL0⟩) with ht₀
    have hsym : (finProdFinEquiv (m := L) (n := L)).symm t₀
        = (⟨0, hL0⟩, ⟨0, hL0⟩) := Equiv.symm_apply_apply _ _
    have hi0 : (((finProdFinEquiv (m := L) (n := L)).symm t₀).1.val) = 0 := by
      simp [hsym]
    have hj0 : (((finProdFinEquiv (m := L) (n := L)).symm t₀).2.val) = 0 := by
      simp [hsym]
    have h0 : gs_e K δ L α' β' γ' E 0 (0 + 1) t₀ = 0 :=
      congrFun (congrFun hcon (⟨0, hM0⟩, ⟨0, hm0⟩)) t₀
    have h0' : gs_e K δ L α' β' γ' E 0 1 t₀ = 0 := h0
    have hle0 := hE 0 1 t₀ hM0 h1m
    obtain ⟨hK0, -, -⟩ := gs_entry K ι haK hbK hcK hα hβ hγ hle0 hH hδH hHα hHβ hHγ
    rw [hi0, hj0] at hK0
    simp only [pow_zero, mul_one] at hK0
    rw [h0'] at hK0
    simp only [map_zero] at hK0
    exact pow_ne_zero E hδK hK0.symm
  -- Entry houses are bounded by `A`.
  have habs : ∀ k l, NumberField.house (algebraMap (𝓞 K) K
      ((fun p : Fin M × Fin m => fun t : Fin (L * L) =>
        gs_e K δ L α' β' γ' E p.1.val (p.2.val + 1) t) k l)) ≤ A := by
    rintro ⟨k', r'⟩ t
    change NumberField.house (algebraMap (𝓞 K) K
      (gs_e K δ L α' β' γ' E k'.val (r'.val + 1) t)) ≤ A
    have hnm : r'.val + 1 ≤ m := r'.is_lt
    have hle1 := hE k'.val (r'.val + 1) t k'.is_lt hnm
    obtain ⟨-, -, hhouse⟩ :=
      gs_entry K ι haK hbK hcK hα hβ hγ hle1 hH hδH hHα hHβ hHγ
    rw [hA]
    have hkp : k'.val ≤ M := le_of_lt k'.is_lt
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1L
    have h2L : (1 : ℝ) ≤ 2 * (L : ℝ) := by
      have hLp : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
      linarith
    calc NumberField.house (algebraMap (𝓞 K) K
          (gs_e K δ L α' β' γ' E k'.val (r'.val + 1) t))
        ≤ H ^ E * (2 * (L : ℝ)) ^ k'.val := hhouse
      _ ≤ H ^ E * (2 * (L : ℝ)) ^ M := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hH0 _)
          exact pow_le_pow_right₀ h2L hkp
  have hcardα : Fintype.card (Fin M × Fin m) = M * m := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hpq : M * m < L * L := by omega
  obtain ⟨ξ, hξne, hΦ0, hξb⟩ := hC₀ (Fin M × Fin m) (Fin (L * L))
    (fun p t => gs_e K δ L α' β' γ' E p.1.val (p.2.val + 1) t)
    hΦne (M * m) (L * L) hp hpq (Fintype.card_fin _) A habs hcardα
  -- The Siegel exponent equals `1`, so the bound collapses.
  have hX0 : ((M * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  have hLq : ((L * L : ℕ) : ℝ) = 2 * ((M * m : ℕ) : ℝ) := by
    rw [hq]; push_cast; ring
  have hexp1 : ((M * m : ℕ) : ℝ) / (((L * L : ℕ) : ℝ) - ((M * m : ℕ) : ℝ)) = 1 := by
    have e : (2 : ℝ) * ((M * m : ℕ) : ℝ) - ((M * m : ℕ) : ℝ)
        = ((M * m : ℕ) : ℝ) := by ring
    rw [hLq, e, div_self hX0]
  have hq2 : ((L * L : ℕ) : ℝ) = (L : ℝ) ^ 2 := by push_cast; ring
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    apply mul_nonneg (pow_nonneg hH0 _)
    apply pow_nonneg
    have hLp : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    linarith
  have hξbound : ∀ t, NumberField.house ((ξ t) : K) ≤ X := by
    intro t
    have h1 : NumberField.house ((ξ t) : K)
        ≤ C₀ * (C₀ * ((L * L : ℕ) : ℝ) * A) := by
      have ht := hξb t
      rw [hexp1, Real.rpow_one] at ht
      exact ht
    calc NumberField.house ((ξ t) : K)
        ≤ C₀ * (C₀ * ((L * L : ℕ) : ℝ) * A) := h1
      _ = C₀ ^ 2 * (((L * L : ℕ) : ℝ) * A) := by ring
      _ ≤ H * (((L * L : ℕ) : ℝ) * A) :=
          mul_le_mul_of_nonneg_right hC₂
            (mul_nonneg (Nat.cast_nonneg _) hA0)
      _ = H * (L : ℝ) ^ 2 * A := by rw [hq2, mul_assoc]
      _ = X := by rw [hX]
  -- Vanishing of the derivatives at the sample points.
  refine ⟨ξ, hξne, hξbound, ?_⟩
  intro k n hkM hn1 hn2
  have hnm : n - 1 < m := by omega
  have hFk : iteratedDeriv k (fun w : ℂ => ∑ t, ι ((ξ t) : K) *
      Complex.exp (gs_ω b L t * w)) ((n : ℂ) * ℓ)
      = ∑ t, ι ((ξ t) : K) * (gs_ω b L t) ^ k *
        Complex.exp (gs_ω b L t * ((n : ℂ) * ℓ)) :=
    gs_iteratedDeriv_expSum k _ _ _
  have hrow : Matrix.mulVec (fun p : Fin M × Fin m => fun t : Fin (L * L) =>
      gs_e K δ L α' β' γ' E p.1.val (p.2.val + 1) t) ξ
      (⟨k, hkM⟩, ⟨n - 1, hnm⟩) = 0 :=
    congrFun hΦ0 _
  have hterm : ∀ t : Fin (L * L), (δ : ℂ) ^ E *
      (ι ((ξ t) : K) * (gs_ω b L t) ^ k *
        Complex.exp (gs_ω b L t * ((n : ℂ) * ℓ)))
      = ι (algebraMap (𝓞 K) K (((fun p : Fin M × Fin m => fun s : Fin (L * L) =>
        gs_e K δ L α' β' γ' E p.1.val (p.2.val + 1) s)
        (⟨k, hkM⟩, ⟨n - 1, hnm⟩)) t * ξ t)) := by
    intro t
    have hle2 := hE k n t hkM hn2
    obtain ⟨-, hC2, -⟩ :=
      gs_entry K ι haK hbK hcK hα hβ hγ hle2 hH hδH hHα hHβ hHγ
    have hexp : Complex.exp (gs_ω b L t * ((n : ℂ) * ℓ))
        = a ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          c ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) := by
      unfold gs_ω
      exact gs_exp_values hℓa hℓc _ _ _
    rw [hexp]
    change (δ : ℂ) ^ E * (ι ((ξ t) : K) * (gs_ω b L t) ^ k *
        (a ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
          c ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)))
      = ι (algebraMap (𝓞 K) K
        (gs_e K δ L α' β' γ' E k (n - 1 + 1) t * ↑(ξ t)))
    rw [Nat.sub_add_cancel hn1, map_mul, map_mul, hC2]
    ring
  have hδE0 : (δ : ℂ) ^ E * iteratedDeriv k (fun w : ℂ => ∑ t, ι ((ξ t) : K) *
      Complex.exp (gs_ω b L t * w)) ((n : ℂ) * ℓ) = 0 := by
    rw [hFk, Finset.mul_sum]
    trans ∑ t : Fin (L * L), ι (algebraMap (𝓞 K) K
      (((fun p : Fin M × Fin m => fun s : Fin (L * L) =>
        gs_e K δ L α' β' γ' E p.1.val (p.2.val + 1) s)
        (⟨k, hkM⟩, ⟨n - 1, hnm⟩)) t * ξ t))
    · exact Finset.sum_congr rfl (fun t _ => hterm t)
    · rw [← map_sum, ← map_sum]
      change ι (algebraMap (𝓞 K) K (Matrix.mulVec
        (fun p : Fin M × Fin m => fun s : Fin (L * L) =>
          gs_e K δ L α' β' γ' E p.1.val (p.2.val + 1) s) ξ
        (⟨k, hkM⟩, ⟨n - 1, hnm⟩))) = 0
      rw [hrow, map_zero, map_zero]
  exact (mul_eq_zero.mp hδE0).resolve_left (pow_ne_zero _ hδC)

/-- Jensen-based analytic estimate for the first
nonvanishing derivative. -/
private theorem gs_upper_bound {b ℓ : ℂ} {L M m T s n₀ : ℕ} {H X : ℝ}
    {u : Fin (L * L) → ℂ} {F : ℂ → ℂ}
    (hb : b ∉ Set.range (algebraMap ℚ ℂ))
    (hℓ : ℓ ≠ 0)
    (hF : ∀ w, F w = ∑ t, u t * Complex.exp (gs_ω b L t * w))
    (hu : ∀ t, ‖u t‖ ≤ X) (hu0 : u ≠ 0) (h1X : 1 ≤ X)
    (hH : 1 ≤ H) (hℓH : ‖ℓ‖ ≤ H) (hbH : ‖b‖ ≤ H)
    (h1L : 1 ≤ L) (h1m : 1 ≤ m) (hn₀1 : 1 ≤ n₀) (hn₀m : n₀ ≤ m)
    (hsM : M ≤ s)
    (hMT : M = L * T) (hTmH : (m : ℝ) * H < (T : ℝ))
    (hvan : ∀ (n k : ℕ), 1 ≤ n → n ≤ m → k < s → iteratedDeriv k F ((n : ℂ) * ℓ) = 0)
    (hne : iteratedDeriv s F ((n₀ : ℂ) * ℓ) ≠ 0) :
    ‖iteratedDeriv s F ((n₀ : ℂ) * ℓ)‖ ≤ (L : ℝ) ^ s *
      ((L : ℝ) ^ 2 * X * Real.exp (2 * H * (s : ℝ) + 2 * (L : ℝ) * (m : ℝ) * H ^ 2)) *
      (((m : ℝ) * H / (T : ℝ)) ^ (s * (m - 1))) := by
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1m
  have hmR0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1L
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  have hLR0 : (0 : ℝ) ≤ (L : ℝ) := le_of_lt hLpos
  have hmH1 : (1 : ℝ) ≤ (m : ℝ) * H := one_le_mul_of_one_le_of_one_le hmR hH
  have hT1 : (1 : ℝ) < (T : ℝ) := lt_of_le_of_lt hmH1 hTmH
  have hT0 : (0 : ℝ) < (T : ℝ) := by linarith
  have hTR0 : (1 : ℝ) ≤ (T : ℝ) := le_of_lt hT1
  have hT1n : 1 ≤ T := Nat.one_le_cast.mp hTR0
  have hM1n : 1 ≤ M := by
    rw [hMT]
    simpa using Nat.mul_le_mul h1L hT1n
  have hs1 : 1 ≤ s := le_trans hM1n hsM
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hsRpos : (0 : ℝ) < (s : ℝ) := by linarith
  have hLR0ne : ((L : ℕ) : ℝ) ≠ 0 := ne_of_gt hLpos
  have hR : (0 : ℝ) < (s : ℝ) / (L : ℝ) := div_pos hsRpos hLpos
  have hTR : (T : ℝ) ≤ (s : ℝ) / (L : ℝ) := by
    rw [le_div_iff₀ hLpos]
    have hsMR : (M : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsM
    have hMR : (M : ℝ) = (L : ℝ) * (T : ℝ) := by rw [hMT]; push_cast; ring
    have e : (T : ℝ) * (L : ℝ) = (L : ℝ) * (T : ℝ) := mul_comm _ _
    linarith
  have hFlam : F = fun w => ∑ t, u t * Complex.exp (gs_ω b L t * w) := funext hF
  have hFdiff : Differentiable ℂ F := by
    rw [hFlam]
    exact gs_expSum_diff u (gs_ω b L)
  have hinj : Function.Injective (gs_ω b L) := gs_freq_injective b hb L
  have hn0Rm : (n₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hn₀m
  have hn₀mem : n₀ ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hn₀1, hn₀m⟩
  have hcP : ((n₀ : ℂ) * ℓ) ∉
      Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀) := by
    intro hmem
    obtain ⟨n, hnmem, hneq⟩ := Finset.mem_image.mp hmem
    have hcc : (n : ℂ) = (n₀ : ℂ) := mul_right_cancel₀ hℓ (by simpa using hneq)
    have hn0 : n = n₀ := by exact_mod_cast hcc
    rw [Finset.mem_erase] at hnmem
    exact hnmem.1 hn0
  have hcast : ∀ a b : ℕ, ((a : ℂ) - (b : ℂ)) = ((((a : ℝ) - (b : ℝ)) : ℝ) : ℂ) := by
    intro a b
    rw [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_natCast]
  have hmem : ∀ n ∈ Finset.Icc 1 m, ‖((n : ℂ) * ℓ - (n₀ : ℂ) * ℓ)‖ ≤ (m : ℝ) * H := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hn.2
    have hnR0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hn0R0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
    have habs : |(n : ℝ) - (n₀ : ℝ)| ≤ (m : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    have e1 : ((n : ℂ) * ℓ - (n₀ : ℂ) * ℓ) = ((((n : ℝ) - (n₀ : ℝ)) : ℝ) : ℂ) * ℓ := by
      rw [← sub_mul]
      congr 1
      exact hcast n n₀
    rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul habs hℓH (norm_nonneg _) (Nat.cast_nonneg _)
  have hPR : ∀ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
      ‖z - (n₀ : ℂ) * ℓ‖ ≤ (s : ℝ) / (L : ℝ) := by
    intro z hz
    obtain ⟨n, hnmem, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_erase, Finset.mem_Icc] at hnmem
    exact (hmem n (Finset.mem_Icc.mpr ⟨hnmem.2.1, hnmem.2.2⟩)).trans
      (le_trans (le_of_lt hTmH) hTR)
  have hzero : ∀ k < s, iteratedDeriv k F ((n₀ : ℂ) * ℓ) = 0 :=
    fun k hk => hvan n₀ k hn₀1 hn₀m hk
  have hPzero : ∀ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
      ∀ k < s, iteratedDeriv k F z = 0 := by
    intro z hz k hk
    obtain ⟨n, hnmem, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_erase, Finset.mem_Icc] at hnmem
    exact hvan n k hnmem.2.1 hnmem.2.2 hk
  have hPne : ∀ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
      ∃ k₀, iteratedDeriv k₀ F z ≠ 0 := by
    intro z hz
    obtain ⟨k, hk⟩ := gs_zero_estimate hinj hu0 z
    refine ⟨k.val, ?_⟩
    rw [hFlam]
    have hN2 := gs_iteratedDeriv_expSum k.val u (gs_ω b L) z
    rw [hN2]
    exact hk
  have hωnorm : ∀ t : Fin (L * L), ‖gs_ω b L t‖ ≤ 2 * (L : ℝ) * H := by
    intro t
    have hiRL : ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℝ)) ≤ (L : ℝ) := by
      exact_mod_cast Nat.le_of_lt (Fin.is_lt _)
    have hjRL : ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℝ)) ≤ (L : ℝ) := by
      exact_mod_cast Nat.le_of_lt (Fin.is_lt _)
    unfold gs_ω
    calc ‖((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℂ) +
          ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℂ)) * b)‖
        ≤ ‖((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℂ))‖ +
          ‖((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℂ)) * b‖ :=
          norm_add_le _ _
      _ = ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℝ)) +
          ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℝ)) * ‖b‖ := by
          rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      _ ≤ (L : ℝ) + (L : ℝ) * H :=
          add_le_add hiRL (mul_le_mul hjRL hbH (norm_nonneg _) (Nat.cast_nonneg _))
      _ ≤ 2 * (L : ℝ) * H := by
          have hLH : (L : ℝ) ≤ (L : ℝ) * H :=
            calc (L : ℝ) = (L : ℝ) * 1 := by ring
              _ ≤ (L : ℝ) * H := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)
          linarith
  have hcnorm : ‖((n₀ : ℂ) * ℓ)‖ ≤ (m : ℝ) * H := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul hn0Rm hℓH (norm_nonneg _) (Nat.cast_nonneg _)
  have hwnorm : ∀ w ∈ Metric.sphere ((n₀ : ℂ) * ℓ) ((s : ℝ) / (L : ℝ)),
      ‖w‖ ≤ (s : ℝ) / (L : ℝ) + (m : ℝ) * H := by
    intro w hw
    have hdist : ‖w - (n₀ : ℂ) * ℓ‖ = (s : ℝ) / (L : ℝ) := by
      have hmem2 := Metric.mem_sphere.mp hw
      rwa [dist_eq_norm] at hmem2
    calc ‖w‖ = ‖(w - (n₀ : ℂ) * ℓ) + (n₀ : ℂ) * ℓ‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - (n₀ : ℂ) * ℓ‖ + ‖(n₀ : ℂ) * ℓ‖ := norm_add_le _ _
      _ ≤ (s : ℝ) / (L : ℝ) + (m : ℝ) * H := add_le_add (le_of_eq hdist) hcnorm
  have hterm0 : ∀ (t : Fin (L * L)) (w : ℂ),
      ‖u t * Complex.exp (gs_ω b L t * w)‖
        ≤ ‖u t‖ * Real.exp (‖gs_ω b L t‖ * ‖w‖) := by
    intro t w
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc ‖Complex.exp (gs_ω b L t * w)‖ ≤ Real.exp ‖gs_ω b L t * w‖ :=
          Complex.norm_exp_le_exp_norm _
      _ = Real.exp (‖gs_ω b L t‖ * ‖w‖) := by rw [norm_mul]
  have hB : (1 : ℝ) ≤ (L : ℝ) ^ 2 * X *
      Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H)) := by
    have harg0 : (0 : ℝ) ≤ 2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H) := by
      positivity
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hLR) h1X
    · exact Real.one_le_exp harg0
  have hbound : ∀ w ∈ Metric.sphere ((n₀ : ℂ) * ℓ) ((s : ℝ) / (L : ℝ)),
      ‖F w‖ ≤ (L : ℝ) ^ 2 * X *
        Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H)) := by
    intro w hw
    rw [hFlam]
    change ‖∑ t : Fin (L * L), u t * Complex.exp (gs_ω b L t * w)‖ ≤ _
    have hterm_le : ∀ t : Fin (L * L), ‖u t‖ * Real.exp (‖gs_ω b L t‖ * ‖w‖)
        ≤ X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H)) := by
      intro t
      have e1 : ‖u t‖ * Real.exp (‖gs_ω b L t‖ * ‖w‖)
          ≤ X * Real.exp (‖gs_ω b L t‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_right (hu t) (le_of_lt (Real.exp_pos _))
      have e2 : (‖gs_ω b L t‖ * ‖w‖)
          ≤ (2 * (L : ℝ) * H) * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H) :=
        mul_le_mul (hωnorm t) (hwnorm w hw) (norm_nonneg _) (by positivity)
      have e3 : Real.exp (‖gs_ω b L t‖ * ‖w‖)
          ≤ Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H)) :=
        Real.exp_le_exp.mpr e2
      calc ‖u t‖ * Real.exp (‖gs_ω b L t‖ * ‖w‖)
          ≤ X * Real.exp (‖gs_ω b L t‖ * ‖w‖) := e1
        _ ≤ X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H)) :=
            mul_le_mul_of_nonneg_left e3 (le_trans zero_le_one h1X)
    calc ‖∑ t : Fin (L * L), u t * Complex.exp (gs_ω b L t * w)‖
        ≤ ∑ t : Fin (L * L), (‖u t‖ * Real.exp (‖gs_ω b L t‖ * ‖w‖)) := by
          refine (norm_sum_le _ _).trans ?_
          exact Finset.sum_le_sum (fun t _ => hterm0 t w)
      _ ≤ ∑ _t : Fin (L * L),
            (X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) :=
          Finset.sum_le_sum (fun t _ => hterm_le t)
      _ = (Finset.univ.card) •
          (X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) := by
          rw [Finset.sum_const]
      _ = ((L * L : ℕ) : ℝ) *
          (X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) := by
          rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (L : ℝ) ^ 2 * X *
          Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H)) := by
          push_cast
          ring
  have hnorm_pos : ∀ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
      0 < ‖(n₀ : ℂ) * ℓ - z‖ := by
    intro z hz
    obtain ⟨n, hnmem, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_erase] at hnmem
    have hne : (n : ℂ) ≠ (n₀ : ℂ) := by
      intro hcon
      exact hnmem.1 (by exact_mod_cast hcon)
    rw [norm_pos_iff, ← sub_mul]
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) hℓ
  have hJensen := gs_jensen_bound F hFdiff ((n₀ : ℂ) * ℓ) ((s : ℝ) / (L : ℝ)) hR s
    ((L : ℝ) ^ 2 * X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) hB
    (Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀))
    hcP hPR hzero hne hPzero hPne hbound
  have hpos1 : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos s
  have hpos2 : (0 : ℝ) < (((s : ℝ) / (L : ℝ)) ^ s) := pow_pos hR s
  have hpos3 : (0 : ℝ) < ∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ)
      ((Finset.Icc 1 m).erase n₀), (((s : ℝ) / (L : ℝ)) / ‖(n₀ : ℂ) * ℓ - z‖) ^ s := by
    apply Finset.prod_pos
    intro z hz
    exact pow_pos (div_pos hR (hnorm_pos z hz)) s
  have hQ : (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
        (‖(n₀ : ℂ) * ℓ - z‖ / ((s : ℝ) / (L : ℝ))) ^ s)
      = (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
        (((s : ℝ) / (L : ℝ)) / ‖(n₀ : ℂ) * ℓ - z‖) ^ s)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro z hz
    rw [← inv_pow, inv_div]
  have s1 : (‖iteratedDeriv s F ((n₀ : ℂ) * ℓ)‖ / (s.factorial : ℝ)) *
        (((s : ℝ) / (L : ℝ)) ^ s)
      ≤ ((L : ℝ) ^ 2 * X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) /
        (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
          (((s : ℝ) / (L : ℝ)) / ‖(n₀ : ℂ) * ℓ - z‖) ^ s) :=
    (le_div_iff₀ hpos3).mpr hJensen
  have s2 : (‖iteratedDeriv s F ((n₀ : ℂ) * ℓ)‖ / (s.factorial : ℝ))
      ≤ ((((L : ℝ) ^ 2 * X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) /
        (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
          (((s : ℝ) / (L : ℝ)) / ‖(n₀ : ℂ) * ℓ - z‖) ^ s)) / (((s : ℝ) / (L : ℝ)) ^ s)) :=
    (le_div_iff₀ hpos2).mpr s1
  have s3 : ‖iteratedDeriv s F ((n₀ : ℂ) * ℓ)‖
      ≤ (((((L : ℝ) ^ 2 * X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) /
        (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
          (((s : ℝ) / (L : ℝ)) / ‖(n₀ : ℂ) * ℓ - z‖) ^ s)) / (((s : ℝ) / (L : ℝ)) ^ s)) *
        (s.factorial : ℝ)) :=
    (div_le_iff₀ hpos1).mp s2
  have hbridge : (((((L : ℝ) ^ 2 * X *
        Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) /
        (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
          (((s : ℝ) / (L : ℝ)) / ‖(n₀ : ℂ) * ℓ - z‖) ^ s)) / (((s : ℝ) / (L : ℝ)) ^ s)) *
        (s.factorial : ℝ))
      = ((s.factorial : ℝ) / (((s : ℝ) / (L : ℝ)) ^ s)) *
        ((L : ℝ) ^ 2 * X * Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))) *
        (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
          (‖(n₀ : ℂ) * ℓ - z‖ / ((s : ℝ) / (L : ℝ))) ^ s) := by
    have hne2 : ((((s : ℝ) / (L : ℝ)) ^ s)) ≠ 0 := ne_of_gt hpos2
    have hne3 : (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
        (((s : ℝ) / (L : ℝ)) / ‖(n₀ : ℂ) * ℓ - z‖) ^ s) ≠ 0 := ne_of_gt hpos3
    rw [hQ, div_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
      inv_eq_one_div, mul_one_div, div_div, mul_comm _ _]
  have hfact : (s.factorial : ℝ) / (((s : ℝ) / (L : ℝ)) ^ s) ≤ (L : ℝ) ^ s := by
    have hFL : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by
      exact_mod_cast Nat.factorial_le_pow s
    rw [div_pow, div_eq_mul_inv, inv_div, ← mul_div_assoc,
      div_le_iff₀ (pow_pos hsRpos s)]
    calc (s.factorial : ℝ) * (L : ℝ) ^ s ≤ (s : ℝ) ^ s * (L : ℝ) ^ s :=
          mul_le_mul_of_nonneg_right hFL (pow_nonneg hLR0 _)
      _ = (L : ℝ) ^ s * (s : ℝ) ^ s := mul_comm _ _
  have hfac : ∀ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
      (‖(n₀ : ℂ) * ℓ - z‖ / ((s : ℝ) / (L : ℝ))) ≤ ((m : ℝ) * H / (T : ℝ)) := by
    intro z hz
    have h1 : ‖(n₀ : ℂ) * ℓ - z‖ ≤ (m : ℝ) * H := by
      rw [norm_sub_rev]
      obtain ⟨n, hnmem, rfl⟩ := Finset.mem_image.mp hz
      change ‖((n : ℂ) * ℓ - (n₀ : ℂ) * ℓ)‖ ≤ (m : ℝ) * H
      rw [Finset.mem_erase, Finset.mem_Icc] at hnmem
      exact hmem n (Finset.mem_Icc.mpr ⟨hnmem.2.1, hnmem.2.2⟩)
    rw [div_le_div_iff₀ hR hT0]
    calc ‖(n₀ : ℂ) * ℓ - z‖ * (T : ℝ) ≤ ((m : ℝ) * H) * (T : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hT0)
      _ ≤ ((m : ℝ) * H) * ((s : ℝ) / (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hTR (mul_nonneg hmR0 hH0)
  have hPcard : (Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀)).card
      = m - 1 := by
    have hinjN : Function.Injective (fun n : ℕ => (n : ℂ) * ℓ) := by
      intro a b hab
      have hcc : (a : ℂ) = (b : ℂ) := mul_right_cancel₀ hℓ (by simpa using hab)
      exact_mod_cast hcc
    rw [Finset.card_image_of_injective _ hinjN, Finset.card_erase_of_mem hn₀mem,
      Nat.card_Icc]
    omega
  have hprod : (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
        (‖(n₀ : ℂ) * ℓ - z‖ / ((s : ℝ) / (L : ℝ))) ^ s)
      ≤ (((((m : ℝ) * H / (T : ℝ)) ^ s) ^
        ((Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀)).card))) := by
    calc (∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
          (‖(n₀ : ℂ) * ℓ - z‖ / ((s : ℝ) / (L : ℝ))) ^ s)
        ≤ ∏ _z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀),
            (((m : ℝ) * H / (T : ℝ)) ^ s) := by
          apply Finset.prod_le_prod₀
          · intro z hz
            exact pow_nonneg (div_nonneg (norm_nonneg _) hR.le) s
          · intro z hz
            exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hR.le) (hfac z hz) s
      _ = (((m : ℝ) * H / (T : ℝ)) ^ s) ^
          ((Finset.image (fun n : ℕ => (n : ℂ) * ℓ) ((Finset.Icc 1 m).erase n₀)).card) := by
          rw [Finset.prod_const]
  have hBexp : Real.exp (2 * (L : ℝ) * H * ((s : ℝ) / (L : ℝ) + (m : ℝ) * H))
      = Real.exp (2 * H * (s : ℝ) + 2 * (L : ℝ) * (m : ℝ) * H ^ 2) := by
    congr 1
    field_simp
  have hBnn : (0 : ℝ) ≤ (L : ℝ) ^ 2 * X *
      Real.exp (2 * H * (s : ℝ) + 2 * (L : ℝ) * (m : ℝ) * H ^ 2) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact sq_nonneg _
      · exact le_trans zero_le_one h1X
    · exact le_of_lt (Real.exp_pos _)
  have hQnn : (0 : ℝ) ≤ ∏ z ∈ Finset.image (fun n : ℕ => (n : ℂ) * ℓ)
      ((Finset.Icc 1 m).erase n₀), (‖(n₀ : ℂ) * ℓ - z‖ / ((s : ℝ) / (L : ℝ))) ^ s :=
    Finset.prod_nonneg (fun z hz => pow_nonneg (div_nonneg (norm_nonneg _) hR.le) s)
  have hLsnn : (0 : ℝ) ≤ (L : ℝ) ^ s := pow_nonneg hLR0 _
  rw [hPcard] at hprod
  rw [← pow_mul] at hprod
  refine s3.trans ?_
  rw [hbridge, hBexp]
  exact mul_le_mul (mul_le_mul hfact (le_refl _) hBnn hLsnn) hprod hQnn
    (mul_nonneg hLsnn hBnn)

/-- Arithmetic lower bound for the first nonvanishing derivative: the value
`γ` cannot be too small, since `δ ^ E'` times `γ` is the image of a nonzero
algebraic integer. -/
private theorem gs_lower_bound (K : Type*) [Field K] [NumberField K]
    {a b c ℓ : ℂ} {δ L m s n₀ d : ℕ} {H X : ℝ}
    {ι : K →+* ℂ} {aK bK cK : K} {α' β' γ' : 𝓞 K}
    {ξ : Fin (L * L) → 𝓞 K} {F : ℂ → ℂ}
    (haK : ι aK = a) (hbK : ι bK = b) (hcK : ι cK = c)
    (hℓa : Complex.exp ℓ = a) (hℓc : Complex.exp (b * ℓ) = c)
    (hα : (α' : K) = δ • aK) (hβ : (β' : K) = δ • bK) (hγ : (γ' : K) = δ • cK)
    (hd : Module.finrank ℚ K = d)
    (hH : 1 ≤ H) (hδH : (δ : ℝ) ≤ H) (h1δ : 1 ≤ δ)
    (hHα : NumberField.house (α' : K) ≤ H)
    (hHβ : NumberField.house (β' : K) ≤ H)
    (hHγ : NumberField.house (γ' : K) ≤ H)
    (hξ : ∀ t, NumberField.house ((ξ t) : K) ≤ X)
    (hn₀m : n₀ ≤ m)
    (hF : ∀ w, F w = ∑ t, ι ((ξ t) : K) * Complex.exp (gs_ω b L t * w))
    (hne : iteratedDeriv s F ((n₀ : ℂ) * ℓ) ≠ 0) :
    1 ≤ H ^ ((s : ℝ) + 2 * (L : ℝ) * (m : ℝ)) *
      ‖iteratedDeriv s F ((n₀ : ℂ) * ℓ)‖ *
      ((L : ℝ) ^ 2 * X * H ^ (2 * (L : ℝ) * (m : ℝ)) *
        (2 * (L : ℝ) * H) ^ s) ^ (d - 1) := by
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hδC : ((δ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- The uniform exponent, and the side condition for the matrix-entry lemma.
  set E' := s + 2 * (L * m) with hE'def
  have hside : ∀ t : Fin (L * L),
      s + ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n₀ +
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n₀ ≤ E' := by
    intro t
    rw [hE'def]
    have hi : ((finProdFinEquiv (m := L) (n := L)).symm t).1.val ≤ L :=
      Nat.le_of_lt (Fin.is_lt _)
    have hj : ((finProdFinEquiv (m := L) (n := L)).symm t).2.val ≤ L :=
      Nat.le_of_lt (Fin.is_lt _)
    have h1 : ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n₀ ≤ L * m :=
      Nat.mul_le_mul hi hn₀m
    have h2 : ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n₀ ≤ L * m :=
      Nat.mul_le_mul hj hn₀m
    omega
  -- The complex value of each entry, and its house bound.
  have hentry : ∀ t : Fin (L * L),
      ι (algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' s n₀ t))
        = (δ : ℂ) ^ E' * ((gs_ω b L t) ^ s *
          a ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n₀) *
          c ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n₀)) :=
    fun t => (gs_entry K ι haK hbK hcK hα hβ hγ (hside t) hH hδH hHα hHβ hHγ).2.1
  have hhouse : ∀ t : Fin (L * L),
      NumberField.house (algebraMap (𝓞 K) K (gs_e K δ L α' β' γ' E' s n₀ t))
        ≤ H ^ E' * (2 * (L : ℝ)) ^ s :=
    fun t => (gs_entry K ι haK hbK hcK hα hβ hγ (hside t) hH hδH hHα hHβ hHγ).2.2
  have hξ' : ∀ t : Fin (L * L),
      NumberField.house (algebraMap (𝓞 K) K (ξ t)) ≤ X := by
    intro t
    have h := hξ t
    rwa [NumberField.RingOfIntegers.coe_eq_algebraMap] at h
  -- The algebraic integer whose image is `δ ^ E'` times the derivative value.
  set Γ : 𝓞 K := ∑ t, ξ t * gs_e K δ L α' β' γ' E' s n₀ t with hΓdef
  have hexp : ∀ t : Fin (L * L), Complex.exp (gs_ω b L t * ((n₀ : ℂ) * ℓ))
      = a ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n₀) *
        c ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n₀) := by
    intro t
    unfold gs_ω
    exact gs_exp_values hℓa hℓc _ _ _
  have hFderiv : iteratedDeriv s F ((n₀ : ℂ) * ℓ)
      = ∑ t, ι ((ξ t : 𝓞 K) : K) * (gs_ω b L t) ^ s *
        Complex.exp (gs_ω b L t * ((n₀ : ℂ) * ℓ)) := by
    have hFlam : F = fun w : ℂ => ∑ t, ι ((ξ t : 𝓞 K) : K) *
        Complex.exp (gs_ω b L t * w) := funext hF
    rw [hFlam]
    exact gs_iteratedDeriv_expSum s _ _ _
  have hterm : ∀ t : Fin (L * L),
      ι (algebraMap (𝓞 K) K (ξ t * gs_e K δ L α' β' γ' E' s n₀ t))
        = (δ : ℂ) ^ E' * (ι ((ξ t : 𝓞 K) : K) * (gs_ω b L t) ^ s *
          Complex.exp (gs_ω b L t * ((n₀ : ℂ) * ℓ))) := by
    intro t
    rw [map_mul, map_mul]
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap (ξ t), hentry t, hexp t]
    ring
  have hbase : ι (algebraMap (𝓞 K) K Γ)
      = (δ : ℂ) ^ E' * iteratedDeriv s F ((n₀ : ℂ) * ℓ) := by
    rw [hΓdef, hFderiv, Finset.mul_sum]
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun t _ => hterm t)
  have hσΓ : ι ((Γ : 𝓞 K) : K)
      = (δ : ℂ) ^ E' * iteratedDeriv s F ((n₀ : ℂ) * ℓ) := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap] at hbase
    exact hbase
  have hΓne : Γ ≠ 0 := by
    intro hcon
    have hδE : ((δ : ℕ) : ℂ) ^ E' ≠ 0 := pow_ne_zero _ hδC
    rw [hcon, map_zero, map_zero] at hbase
    exact (mul_ne_zero hδE hne) hbase.symm
  -- Nonnegativity of the coefficient bound (vacuous when `L = 0`).
  have hX0 : (0 : ℝ) ≤ X := by
    by_cases hL : L = 0
    · subst hL
      exfalso
      apply hΓne
      rw [hΓdef]
      have hcard0 : (Finset.univ : Finset (Fin (0 * 0))).card = 0 := by
        rw [Finset.card_univ, Fintype.card_fin, Nat.zero_mul]
      rw [Finset.card_eq_zero.mp hcard0]
      exact Finset.sum_empty
    · have hpos : 0 < L * L :=
        Nat.mul_pos (Nat.pos_of_ne_zero hL) (Nat.pos_of_ne_zero hL)
      have hne2 : Nonempty (Fin (L * L)) := ⟨⟨0, hpos⟩⟩
      obtain ⟨t⟩ := hne2
      exact (NumberField.house_nonneg _).trans (hξ' t)
  -- The house of `Γ`.
  have hhouseΓ : NumberField.house ((Γ : 𝓞 K) : K)
      ≤ (L : ℝ) ^ 2 * X * H ^ E' * (2 * (L : ℝ)) ^ s := by
    have hle : NumberField.house (algebraMap (𝓞 K) K Γ)
        ≤ (L : ℝ) ^ 2 * X * H ^ E' * (2 * (L : ℝ)) ^ s := by
      rw [hΓdef, map_sum]
      refine (NumberField.house_sum_le_sum_house _ _).trans ?_
      have hsum : ∑ t, NumberField.house (algebraMap (𝓞 K) K
          (ξ t * gs_e K δ L α' β' γ' E' s n₀ t))
          ≤ ∑ _t : Fin (L * L), X * (H ^ E' * (2 * (L : ℝ)) ^ s) := by
        apply Finset.sum_le_sum
        intro t _
        rw [map_mul]
        exact (NumberField.house_mul_le _ _).trans
          (mul_le_mul (hξ' t) (hhouse t) (NumberField.house_nonneg _) hX0)
      refine hsum.trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_of_eq (by push_cast; ring)
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact hle
  -- Liouville, and conversion of the norm and house bounds to real powers.
  have hliou := gs_liouville K ι Γ hΓne
    ((L : ℝ) ^ 2 * X * H ^ E' * (2 * (L : ℝ)) ^ s) hhouseΓ
  rw [hd] at hliou
  have hEcast : ((E' : ℕ) : ℝ) = (s : ℝ) + 2 * (L : ℝ) * (m : ℝ) := by
    rw [hE'def]
    push_cast
    ring
  have hnorm : ‖ι ((Γ : 𝓞 K) : K)‖
      ≤ H ^ ((s : ℝ) + 2 * (L : ℝ) * (m : ℝ)) *
        ‖iteratedDeriv s F ((n₀ : ℂ) * ℓ)‖ := by
    rw [hσΓ, norm_mul, norm_pow, Complex.norm_natCast]
    have h2 : (δ : ℝ) ^ E' ≤ H ^ E' :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hδH _
    have h3 : (H : ℝ) ^ E' = H ^ ((s : ℝ) + 2 * (L : ℝ) * (m : ℝ)) := by
      rw [← hEcast, Real.rpow_natCast]
    rw [h3] at h2
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hY0 : (0 : ℝ) ≤ (L : ℝ) ^ 2 * X * H ^ E' * (2 * (L : ℝ)) ^ s :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hX0) (pow_nonneg hH0 _))
      (pow_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (Nat.cast_nonneg _)) _)
  have hYeq : (L : ℝ) ^ 2 * X * H ^ E' * (2 * (L : ℝ)) ^ s
      = (L : ℝ) ^ 2 * X * H ^ (2 * (L : ℝ) * (m : ℝ)) * (2 * (L : ℝ) * H) ^ s := by
    have e1 : (H : ℝ) ^ E' = H ^ (2 * (L : ℝ) * (m : ℝ)) * H ^ ((s : ℕ) : ℝ) := by
      have hrw : (H : ℝ) ^ E' = H ^ (((E' : ℕ)) : ℝ) :=
        (Real.rpow_natCast H E').symm
      rw [hrw, hEcast, Real.rpow_add hHpos]
      exact mul_comm _ _
    have e2 : (2 * (L : ℝ) * H) ^ s = (2 * (L : ℝ)) ^ s * H ^ ((s : ℕ) : ℝ) := by
      rw [mul_pow, Real.rpow_natCast]
    rw [e1, e2]
    ring
  have hfin : ‖ι ((Γ : 𝓞 K) : K)‖
      * ((L : ℝ) ^ 2 * X * H ^ E' * (2 * (L : ℝ)) ^ s) ^ (d - 1)
      ≤ (H ^ ((s : ℝ) + 2 * (L : ℝ) * (m : ℝ)) *
          ‖iteratedDeriv s F ((n₀ : ℂ) * ℓ)‖) *
        ((L : ℝ) ^ 2 * X * H ^ (2 * (L : ℝ) * (m : ℝ))
          * (2 * (L : ℝ) * H) ^ s) ^ (d - 1) := by
    have hB : ((L : ℝ) ^ 2 * X * H ^ E' * (2 * (L : ℝ)) ^ s) ^ (d - 1)
        ≤ ((L : ℝ) ^ 2 * X * H ^ (2 * (L : ℝ) * (m : ℝ))
          * (2 * (L : ℝ) * H) ^ s) ^ (d - 1) := by
      rw [hYeq]
    exact mul_le_mul hnorm hB (pow_nonneg hY0 _)
      (mul_nonneg (Real.rpow_nonneg hH0 _) (norm_nonneg _))
  exact hliou.trans hfin

end GS_DEFS

section GS_ARITH

/-- The `Q` factor is bounded by `Y ^ M`, and `Y ^ M ≤ Y ^ s`. -/
private theorem gs_arith_Q
    {H L X : ℝ} {m d s : ℕ} {M : ℝ}
    (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hd : 1 ≤ d)
    (hMs : M ≤ (s : ℝ))
    (h2Lm : 2 * L * (m : ℝ) ≤ M)
    (hX0 : 0 ≤ X)
    (hLX : L ^ 2 * X ≤ (H ^ 3 * (2 * L) ^ 2) ^ M) :
    H ^ (2 * L * (m : ℝ) * (d : ℝ)) * Real.exp (2 * L * (m : ℝ) * H ^ 2)
        * (L ^ 2 * X) ^ d
      ≤ (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ M
    ∧ (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ M
      ≤ (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ s := by
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have h2L0 : (0 : ℝ) ≤ 2 * L := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hZ0 : (0 : ℝ) ≤ H ^ 3 * (2 * L) ^ 2 :=
    mul_nonneg (pow_nonneg hH0 _) (pow_nonneg h2L0 _)
  have hY1 : 1 ≤ H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d) := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · exact one_le_pow₀ hH
      · exact Real.one_le_exp (sq_nonneg H)
    · apply one_le_pow₀
      linarith
  have hY2 : (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ M
      ≤ (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ s := by
    rw [← Real.rpow_natCast _ s]
    exact Real.rpow_le_rpow_of_exponent_le hY1 hMs
  have hLXnn : (0 : ℝ) ≤ L ^ 2 * X := mul_nonneg (sq_nonneg L) hX0
  have step1 : (L ^ 2 * X) ^ d ≤ ((H ^ 3 * (2 * L) ^ 2) ^ M) ^ d :=
    pow_le_pow_left₀ hLXnn hLX d
  have step2 : (((H ^ 3 * (2 * L) ^ 2) ^ M) ^ d : ℝ)
      = (H ^ 3 * (2 * L) ^ 2) ^ (M * (d : ℝ)) := by
    rw [← Real.rpow_natCast _ d, ← Real.rpow_mul hZ0]
  have step3 : ((H ^ 3 * (2 * L) ^ 2) ^ (M * (d : ℝ)) : ℝ)
      = H ^ (3 * (M * (d : ℝ))) * (2 * L) ^ (2 * (M * (d : ℝ))) := by
    rw [Real.mul_rpow (pow_nonneg hH0 3) (pow_nonneg h2L0 2),
      ← Real.rpow_natCast H 3, ← Real.rpow_natCast (2 * L) 2,
      ← Real.rpow_mul hH0, ← Real.rpow_mul h2L0]
    have c3 : ((3 : ℕ) : ℝ) * (M * (d : ℝ)) = 3 * (M * (d : ℝ)) := by
      push_cast; ring
    have c2 : ((2 : ℕ) : ℝ) * (M * (d : ℝ)) = 2 * (M * (d : ℝ)) := by
      push_cast; ring
    rw [c3, c2]
  have hLXb : (L ^ 2 * X) ^ d
      ≤ H ^ (3 * (M * (d : ℝ))) * (2 * L) ^ (2 * (M * (d : ℝ))) := by
    rw [← step3, ← step2]
    exact step1
  have step5 : Real.exp (2 * L * (m : ℝ) * H ^ 2) ≤ Real.exp (H ^ 2 * M) := by
    apply Real.exp_le_exp.mpr
    rw [mul_comm (H ^ 2) M]
    exact mul_le_mul_of_nonneg_right h2Lm (sq_nonneg H)
  have step6 : 2 * L * (m : ℝ) * (d : ℝ) + 3 * (M * (d : ℝ))
      ≤ 4 * (d : ℝ) * M := by
    have h := mul_le_mul_of_nonneg_right h2Lm hd0
    have h2 : M * (d : ℝ) = (d : ℝ) * M := mul_comm _ _
    linarith
  have eH : H ^ (2 * L * (m : ℝ) * (d : ℝ) + 3 * (M * (d : ℝ)))
      ≤ H ^ (4 * (d : ℝ) * M) :=
    Real.rpow_le_rpow_of_exponent_le hH step6
  have e2 : (2 * L) ^ (2 * (M * (d : ℝ))) = (2 * L) ^ (2 * (d : ℝ) * M) := by
    congr 1; ring
  have eY : (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ M
      = H ^ (4 * (d : ℝ) * M) * Real.exp (H ^ 2 * M)
        * (2 * L) ^ (2 * (d : ℝ) * M) := by
    have c1 : ((4 * d : ℕ) : ℝ) * M = 4 * (d : ℝ) * M := by push_cast; ring
    have c2 : ((2 * d : ℕ) : ℝ) * M = 2 * (d : ℝ) * M := by push_cast; ring
    rw [Real.mul_rpow (mul_nonneg (pow_nonneg hH0 _) (le_of_lt (Real.exp_pos _)))
        (pow_nonneg h2L0 _),
      Real.mul_rpow (pow_nonneg hH0 _) (le_of_lt (Real.exp_pos _)),
      ← Real.rpow_natCast H (4 * d), ← Real.rpow_mul hH0,
      ← Real.rpow_natCast (2 * L) (2 * d), ← Real.rpow_mul h2L0,
      ← Real.exp_mul, c1, c2]
  have hpos1 : (0 : ℝ)
      ≤ H ^ (2 * L * (m : ℝ) * (d : ℝ)) * Real.exp (2 * L * (m : ℝ) * H ^ 2) :=
    mul_nonneg (Real.rpow_nonneg hH0 _) (le_of_lt (Real.exp_pos _))
  have g1 : H ^ (2 * L * (m : ℝ) * (d : ℝ)) * H ^ (3 * (M * (d : ℝ)))
      ≤ H ^ (4 * (d : ℝ) * M) := by
    have q3 : H ^ (2 * L * (m : ℝ) * (d : ℝ)) * H ^ (3 * (M * (d : ℝ)))
        = H ^ (2 * L * (m : ℝ) * (d : ℝ) + 3 * (M * (d : ℝ))) :=
      (Real.rpow_add hHpos _ _).symm
    rw [q3]; exact eH
  have hfin : H ^ (2 * L * (m : ℝ) * (d : ℝ)) * Real.exp (2 * L * (m : ℝ) * H ^ 2)
        * (L ^ 2 * X) ^ d
      ≤ H ^ (4 * (d : ℝ) * M) * Real.exp (H ^ 2 * M)
        * (2 * L) ^ (2 * (d : ℝ) * M) := by
    calc H ^ (2 * L * (m : ℝ) * (d : ℝ)) * Real.exp (2 * L * (m : ℝ) * H ^ 2)
            * (L ^ 2 * X) ^ d
        ≤ H ^ (2 * L * (m : ℝ) * (d : ℝ)) * Real.exp (2 * L * (m : ℝ) * H ^ 2)
            * (H ^ (3 * (M * (d : ℝ))) * (2 * L) ^ (2 * (M * (d : ℝ)))) :=
          mul_le_mul_of_nonneg_left hLXb hpos1
      _ = (H ^ (2 * L * (m : ℝ) * (d : ℝ)) * H ^ (3 * (M * (d : ℝ))))
            * Real.exp (2 * L * (m : ℝ) * H ^ 2) * (2 * L) ^ (2 * (M * (d : ℝ))) := by
          ring
      _ ≤ H ^ (4 * (d : ℝ) * M) * Real.exp (H ^ 2 * M)
            * (2 * L) ^ (2 * (M * (d : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg h2L0 _)
          exact (mul_le_mul_of_nonneg_right g1 (le_of_lt (Real.exp_pos _))).trans
            (mul_le_mul_of_nonneg_left step5 (Real.rpow_nonneg hH0 _))
      _ = H ^ (4 * (d : ℝ) * M) * Real.exp (H ^ 2 * M)
            * (2 * L) ^ (2 * (d : ℝ) * M) := by rw [e2]
  exact ⟨by rw [eY]; exact hfin, hY2⟩

/-- `Z₁ * Y ≤ K₀ / T`, via cancellation of `T ^ (3 * d)`. -/
private theorem gs_arith_ZY
    {H L T : ℝ} {m d : ℕ}
    (hH : 1 ≤ H) (hT : 0 < T) (hd : 1 ≤ d)
    (hm : m = 3 * d + 2)
    (hL : L = 2 * (m : ℝ) * T) :
    H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1) * (((m : ℝ) * H) / T) ^ (m - 1)
      * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d))
    ≤ (H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
        * (((m : ℝ) * H) ^ (3 * d + 1))) / T := by
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hT0 : (0 : ℝ) ≤ T := le_of_lt hT
  have hL0 : (0 : ℝ) ≤ L := by
    rw [hL]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hT0
  have h2L0 : (0 : ℝ) ≤ 2 * L := by linarith
  have hm1 : m - 1 = 3 * d + 1 := by omega
  have hA : H * H ^ (d - 1) * H ^ (4 * d) = H ^ (5 * d) := by
    have h5 : 1 + ((d - 1) + 4 * d) = 5 * d := by omega
    calc H * H ^ (d - 1) * H ^ (4 * d)
        = H ^ 1 * (H ^ (d - 1) * H ^ (4 * d)) := by rw [pow_one, mul_assoc]
      _ = H ^ 1 * H ^ ((d - 1) + 4 * d) := by rw [← pow_add]
      _ = H ^ (1 + ((d - 1) + 4 * d)) := by rw [← pow_add]
      _ = H ^ (5 * d) := by rw [h5]
  have e1 : H * (2 * L * H) ^ (d - 1) * H ^ (4 * d)
      = H ^ (5 * d) * (2 * L) ^ (d - 1) := by
    rw [mul_pow]
    calc H * ((2 * L) ^ (d - 1) * H ^ (d - 1)) * H ^ (4 * d)
        = (H * H ^ (d - 1) * H ^ (4 * d)) * (2 * L) ^ (d - 1) := by ring
      _ = H ^ (5 * d) * (2 * L) ^ (d - 1) := by rw [hA]
  have h3 : (d - 1) + 2 * d + 1 = 3 * d := by omega
  have e2 : L * (2 * L) ^ (d - 1) * (2 * L) ^ (2 * d)
      ≤ (2 * L) ^ (3 * d) := by
    calc L * (2 * L) ^ (d - 1) * (2 * L) ^ (2 * d)
        = L * ((2 * L) ^ (d - 1) * (2 * L) ^ (2 * d)) := by rw [mul_assoc]
      _ = L * (2 * L) ^ ((d - 1) + 2 * d) := by rw [← pow_add]
      _ ≤ (2 * L) * (2 * L) ^ ((d - 1) + 2 * d) :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg h2L0 _)
      _ = (2 * L) ^ (((d - 1) + 2 * d) + 1) := by rw [pow_succ']
      _ = (2 * L) ^ (3 * d) := by rw [h3]
  have e3 : Real.exp (2 * H) * Real.exp (H ^ 2) = Real.exp (2 * H + H ^ 2) :=
    (Real.exp_add _ _).symm
  have e4 : (((m : ℝ) * H) / T) ^ (m - 1)
      = ((m : ℝ) * H) ^ (3 * d + 1) / T ^ (3 * d + 1) := by
    rw [hm1, div_pow]
  have e5 : (2 * L) ^ (3 * d) = (4 * (m : ℝ)) ^ (3 * d) * T ^ (3 * d) := by
    have h2L : (2 : ℝ) * L = (4 * (m : ℝ)) * T := by rw [hL]; ring
    rw [h2L, mul_pow]
  have posE : (0 : ℝ) ≤ Real.exp (2 * H + H ^ 2) := le_of_lt (Real.exp_pos _)
  have posH5 : (0 : ℝ) ≤ H ^ (5 * d) := pow_nonneg hH0 _
  have posD : (0 : ℝ) ≤ ((m : ℝ) * H) ^ (3 * d + 1) / T ^ (3 * d + 1) :=
    div_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hH0) _)
      (pow_nonneg hT0 _)
  have hT3 : T ^ (3 * d) ≠ 0 := pow_ne_zero _ (ne_of_gt hT)
  have stepA : H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
        * (((m : ℝ) * H) / T) ^ (m - 1)
        * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d))
      = (H ^ (5 * d) * (2 * L) ^ (d - 1)) * (L * (2 * L) ^ (2 * d))
        * Real.exp (2 * H + H ^ 2)
        * (((m : ℝ) * H) ^ (3 * d + 1) / T ^ (3 * d + 1)) := by
    have rearr : H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
          * (((m : ℝ) * H) / T) ^ (m - 1)
          * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d))
        = (H * (2 * L * H) ^ (d - 1) * H ^ (4 * d))
          * (L * (2 * L) ^ (2 * d))
          * (Real.exp (2 * H) * Real.exp (H ^ 2))
          * ((((m : ℝ) * H) / T) ^ (m - 1)) := by ring
    rw [rearr, e1, e3, e4]
  have stepB : (H ^ (5 * d) * (2 * L) ^ (d - 1)) * (L * (2 * L) ^ (2 * d))
        * Real.exp (2 * H + H ^ 2)
        * (((m : ℝ) * H) ^ (3 * d + 1) / T ^ (3 * d + 1))
      ≤ (H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (2 * L) ^ (3 * d))
        * (((m : ℝ) * H) ^ (3 * d + 1) / T ^ (3 * d + 1)) := by
    apply mul_le_mul_of_nonneg_right _ posD
    have rearr2 : (H ^ (5 * d) * (2 * L) ^ (d - 1)) * (L * (2 * L) ^ (2 * d))
          * Real.exp (2 * H + H ^ 2)
        = (H ^ (5 * d) * Real.exp (2 * H + H ^ 2))
          * (L * (2 * L) ^ (d - 1) * (2 * L) ^ (2 * d)) := by ring
    rw [rearr2]
    exact mul_le_mul_of_nonneg_left e2 (mul_nonneg posH5 posE)
  have stepC : (H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (2 * L) ^ (3 * d))
        * (((m : ℝ) * H) ^ (3 * d + 1) / T ^ (3 * d + 1))
      = (H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
          * (((m : ℝ) * H) ^ (3 * d + 1))) * T ^ (3 * d) / T ^ (3 * d + 1) := by
    rw [e5]; ring
  have hps : T ^ (3 * d + 1) = T ^ (3 * d) * T := pow_succ T (3 * d)
  have stepD : (H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
          * (((m : ℝ) * H) ^ (3 * d + 1))) * T ^ (3 * d) / T ^ (3 * d + 1)
      ≤ (H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
          * (((m : ℝ) * H) ^ (3 * d + 1))) / T := by
    rw [hps, div_le_div_iff₀ (mul_pos (pow_pos hT _) hT) hT]
    exact le_of_eq (by ring)
  calc H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
          * (((m : ℝ) * H) / T) ^ (m - 1)
          * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d))
      = _ := stepA
    _ ≤ _ := stepB
    _ = _ := stepC
    _ ≤ _ := stepD

/-- The final arithmetic contradiction: the upper bound substituted into the
lower bound regroups to `1 ≤ Z₁ ^ s * Q`,
which contradicts `Z₁ ^ s * Q ≤ (Z₁ * Y) ^ s < 1`. -/
private theorem gs_arith_final
    {H T L M X g : ℝ} {d m s : ℕ}
    (hH : 1 ≤ H) (hd : 1 ≤ d) (hm : m = 3 * d + 2)
    (hK : H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
      * (((m : ℝ) * H) ^ (3 * d + 1)) < T)
    (hL : L = 2 * (m : ℝ) * T) (hM : M = 2 * (m : ℝ) * T ^ 2)
    (hsM : M ≤ (s : ℝ))
    (hX : X = H * L ^ 2 * H ^ (M + 2 * L * (m : ℝ)) * (2 * L) ^ M)
    (hU : g ≤ L ^ s
      * (L ^ 2 * X * Real.exp (2 * H * (s : ℝ) + 2 * L * (m : ℝ) * H ^ 2))
      * ((((m : ℝ) * H) / T) ^ (s * (m - 1))))
    (hLo : 1 ≤ H ^ ((s : ℝ) + 2 * L * (m : ℝ)) * g
      * (L ^ 2 * X * H ^ (2 * L * (m : ℝ)) * (2 * L * H) ^ s) ^ (d - 1)) :
    False := by
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hmR0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hm5 : 5 ≤ m := by omega
  have hmR5 : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm5
  have hAB : (1 : ℝ) ≤ H ^ (5 * d) * Real.exp (2 * H + H ^ 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH)
      (Real.one_le_exp (by linarith [sq_nonneg H]))
  have hD1 : (1 : ℝ) ≤ ((m : ℝ) * H) ^ (3 * d + 1) :=
    one_le_pow₀
      (one_le_mul_of_one_le_of_one_le (by linarith [hmR5]) hH)
  have hK01 : 1 ≤ H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
      * (((m : ℝ) * H) ^ (3 * d + 1)) := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · apply one_le_mul_of_one_le_of_one_le
        · exact one_le_pow₀ hH
        · exact Real.one_le_exp (by linarith [sq_nonneg H])
      · exact one_le_pow₀ (by linarith [hmR5])
    · exact hD1
  have hT1 : (1 : ℝ) < T := lt_of_le_of_lt hK01 hK
  have hT : (0 : ℝ) < T := by linarith
  have hT0 : (0 : ℝ) ≤ T := le_of_lt hT
  have hC0 : (0 : ℝ) ≤ (4 * (m : ℝ)) ^ (3 * d) :=
    pow_nonneg (by linarith [hmR5]) _
  have hKC1 : (4 * (m : ℝ)) ^ (3 * d)
      ≤ (H ^ (5 * d) * Real.exp (2 * H + H ^ 2)) * (4 * (m : ℝ)) ^ (3 * d) :=
    le_mul_of_one_le_left hC0 hAB
  have hKC : (4 * (m : ℝ)) ^ (3 * d)
      ≤ H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
        * (((m : ℝ) * H) ^ (3 * d + 1)) :=
    le_trans hKC1
      (le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg (pow_nonneg hH0 _)
          (le_of_lt (Real.exp_pos _))) hC0) hD1)
  have h4 : (4 : ℝ) * (m : ℝ) ≤ (4 * (m : ℝ)) ^ (3 * d) :=
    le_self_pow₀ (by linarith [hmR5]) (by omega)
  have hT2m : 2 * (m : ℝ) < T := by linarith [hK, hKC, h4, hmR0]
  have hL0 : (0 : ℝ) ≤ L := by
    rw [hL]
    exact mul_nonneg (mul_nonneg (by norm_num) hmR0) hT0
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h2m : (1 : ℝ) ≤ 2 * (m : ℝ) := by linarith [hmR5]
    exact one_le_mul_of_one_le_of_one_le h2m (le_of_lt hT1)
  have h2L0 : (0 : ℝ) ≤ 2 * L := by linarith
  have h2Lpos : (0 : ℝ) < 2 * L := by linarith [hL1]
  have hT2 : (1 : ℝ) ≤ T ^ 2 := one_le_pow₀ (le_of_lt hT1)
  have hM4 : (4 : ℝ) ≤ M := by
    rw [hM]
    have h2m10 : (10 : ℝ) ≤ 2 * (m : ℝ) := by linarith [hmR5]
    have h := mul_le_mul_of_nonneg_right h2m10 (sq_nonneg T)
    linarith [h, hT2]
  have hM1 : (1 : ℝ) ≤ M := by linarith [hM4]
  have h2Lm : 2 * L * (m : ℝ) ≤ M := by
    have hnn : (0 : ℝ) ≤ (2 * (m : ℝ) * T) * (T - 2 * (m : ℝ)) :=
      mul_nonneg (mul_nonneg (by linarith [hmR0]) hT0) (by linarith [hT2m])
    have heq : (2 : ℝ) * (2 * (m : ℝ) * T) * (m : ℝ)
        + (2 * (m : ℝ) * T) * (T - 2 * (m : ℝ)) = 2 * (m : ℝ) * T ^ 2 := by
      ring
    rw [hM, hL]
    linarith [hnn, heq]
  have hX0 : (0 : ℝ) ≤ X := by
    rw [hX]
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg hH0 (sq_nonneg L)
      · exact Real.rpow_nonneg hH0 _
    · exact Real.rpow_nonneg h2L0 _
  have eHexp : (1 : ℝ) + (M + 2 * L * (m : ℝ)) ≤ 3 * M := by
    linarith [h2Lm, hM1]
  have hHe : H ^ (1 + (M + 2 * L * (m : ℝ))) ≤ H ^ (3 * M) :=
    Real.rpow_le_rpow_of_exponent_le hH eHexp
  have h4M : ((4 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM4
  have hL4 : L ^ 4 ≤ (2 * L) ^ M := by
    have h1 : (2 * L) ^ (4 : ℕ) ≤ (2 * L) ^ M := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [hL1]) h4M
    calc L ^ 4 ≤ (2 * L) ^ 4 :=
          pow_le_pow_left₀ hL0 (by linarith) 4
      _ ≤ (2 * L) ^ M := h1
  have hsplit : L ^ 2 * X
      = H ^ (1 + (M + 2 * L * (m : ℝ))) * L ^ 4 * (2 * L) ^ M := by
    have hH1 : (H : ℝ) = H ^ ((1 : ℝ)) := (Real.rpow_one H).symm
    have rearr : L ^ 2 * (H ^ ((1 : ℝ)) * L ^ 2 * H ^ (M + 2 * L * (m : ℝ))
        * (2 * L) ^ M)
        = (H ^ ((1 : ℝ)) * H ^ (M + 2 * L * (m : ℝ))) * (L ^ 2 * L ^ 2)
          * (2 * L) ^ M := by ring
    rw [hX]
    nth_rewrite 1 [hH1]
    rw [rearr, ← Real.rpow_add hHpos]
    ring
  have hY3 : ((H ^ 3 * (2 * L) ^ 2) ^ M : ℝ)
      = H ^ (3 * M) * ((2 * L) ^ M * (2 * L) ^ M) := by
    have c3 : ((3 : ℕ) : ℝ) * M = 3 * M := by push_cast; ring
    have hMM : ((2 : ℕ) : ℝ) * M = M + M := by push_cast; ring
    rw [Real.mul_rpow (pow_nonneg hH0 3) (pow_nonneg h2L0 2),
      ← Real.rpow_natCast H 3, ← Real.rpow_natCast (2 * L) 2,
      ← Real.rpow_mul hH0, ← Real.rpow_mul h2L0, c3, hMM,
      Real.rpow_add h2Lpos]
  have hLX : L ^ 2 * X ≤ (H ^ 3 * (2 * L) ^ 2) ^ M := by
    rw [hsplit, hY3]
    have hA := mul_le_mul_of_nonneg_right hHe
      (show (0 : ℝ) ≤ L ^ 4 * (2 * L) ^ M from
        mul_nonneg (pow_nonneg hL0 4) (Real.rpow_nonneg h2L0 M))
    have hB := mul_le_mul_of_nonneg_left hL4
      (show (0 : ℝ) ≤ H ^ (3 * M) * (2 * L) ^ M from
        mul_nonneg (Real.rpow_nonneg hH0 _) (Real.rpow_nonneg h2L0 _))
    calc H ^ (1 + (M + 2 * L * (m : ℝ))) * L ^ 4 * (2 * L) ^ M
        = H ^ (1 + (M + 2 * L * (m : ℝ))) * (L ^ 4 * (2 * L) ^ M) := by ring
      _ ≤ H ^ (3 * M) * (L ^ 4 * (2 * L) ^ M) := hA
      _ = (H ^ (3 * M) * (2 * L) ^ M) * L ^ 4 := by ring
      _ ≤ (H ^ (3 * M) * (2 * L) ^ M) * (2 * L) ^ M := hB
      _ = H ^ (3 * M) * ((2 * L) ^ M * (2 * L) ^ M) := by ring
  have h2LH0 : (0 : ℝ) ≤ 2 * L * H :=
    mul_nonneg (mul_nonneg (by norm_num) hL0) hH0
  have hnn1 : (0 : ℝ) ≤ H ^ ((s : ℝ) + 2 * L * (m : ℝ)) :=
    Real.rpow_nonneg hH0 _
  have hnn2 : (0 : ℝ)
      ≤ (L ^ 2 * X * H ^ (2 * L * (m : ℝ)) * (2 * L * H) ^ s) ^ (d - 1) := by
    apply pow_nonneg
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (sq_nonneg L) hX0
      · exact Real.rpow_nonneg hH0 _
    · exact pow_nonneg h2LH0 _
  have hsub : H ^ ((s : ℝ) + 2 * L * (m : ℝ)) * g
        * (L ^ 2 * X * H ^ (2 * L * (m : ℝ)) * (2 * L * H) ^ s) ^ (d - 1)
      ≤ H ^ ((s : ℝ) + 2 * L * (m : ℝ))
        * (L ^ s
          * (L ^ 2 * X * Real.exp (2 * H * (s : ℝ) + 2 * L * (m : ℝ) * H ^ 2))
          * (((((m : ℝ) * H) / T) ^ (s * (m - 1)))))
        * (L ^ 2 * X * H ^ (2 * L * (m : ℝ)) * (2 * L * H) ^ s) ^ (d - 1) := by
    apply mul_le_mul_of_nonneg_right _ hnn2
    exact mul_le_mul_of_nonneg_left hU hnn1
  have r1 : H ^ ((s : ℝ) + 2 * L * (m : ℝ)) = H ^ s * H ^ (2 * L * (m : ℝ)) := by
    rw [Real.rpow_add hHpos, Real.rpow_natCast]
  have r2 : Real.exp (2 * H * (s : ℝ) + 2 * L * (m : ℝ) * H ^ 2)
      = (Real.exp (2 * H)) ^ s * Real.exp (2 * L * (m : ℝ) * H ^ 2) := by
    have e : 2 * H * (s : ℝ) = (s : ℝ) * (2 * H) := by ring
    rw [Real.exp_add, e, Real.exp_nat_mul]
  have r3 : ((((m : ℝ) * H) / T) ^ (s * (m - 1)))
      = ((((m : ℝ) * H) / T) ^ (m - 1)) ^ s := by
    rw [← pow_mul]; congr 1; exact mul_comm _ _
  have r4 : (((2 * L * H) ^ s) ^ ((d - 1) : ℕ))
      = ((((2 * L * H) ^ ((d - 1) : ℕ)) ^ s)) := by
    rw [← pow_mul, ← pow_mul]; congr 1; exact mul_comm _ _
  have r5 : (L ^ 2 * X) * (L ^ 2 * X) ^ ((d - 1) : ℕ) = (L ^ 2 * X) ^ d := by
    nth_rewrite 1 [← pow_one (L ^ 2 * X)]
    rw [← pow_add]
    congr 1
    omega
  have r6 : (H ^ (2 * L * (m : ℝ))) ^ ((d - 1) : ℕ)
      = H ^ (2 * L * (m : ℝ) * ((d : ℝ) - 1)) := by
    rw [← Real.rpow_natCast _ (d - 1), ← Real.rpow_mul hH0, Nat.cast_sub hd,
      Nat.cast_one]
  have r7a : H ^ (2 * L * (m : ℝ)) * H ^ (2 * L * (m : ℝ) * ((d : ℝ) - 1))
      = H ^ (2 * L * (m : ℝ) * (d : ℝ)) := by
    rw [← Real.rpow_add hHpos]; congr 1; ring
  have zexp : (H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
        * ((((m : ℝ) * H) / T) ^ (m - 1))) ^ s
      = H ^ s * L ^ s * (Real.exp (2 * H)) ^ s * (((2 * L * H) ^ (d - 1)) ^ s)
        * (((((m : ℝ) * H) / T) ^ (m - 1)) ^ s) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow]
  have hreg : H ^ ((s : ℝ) + 2 * L * (m : ℝ))
        * (L ^ s
          * (L ^ 2 * X * Real.exp (2 * H * (s : ℝ) + 2 * L * (m : ℝ) * H ^ 2))
          * (((((m : ℝ) * H) / T) ^ (s * (m - 1)))))
        * (L ^ 2 * X * H ^ (2 * L * (m : ℝ)) * (2 * L * H) ^ s) ^ (d - 1)
      = (H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
          * ((((m : ℝ) * H) / T) ^ (m - 1))) ^ s
        * (H ^ (2 * L * (m : ℝ) * (d : ℝ))
          * Real.exp (2 * L * (m : ℝ) * H ^ 2) * (L ^ 2 * X) ^ d) := by
    conv_lhs => rw [r1, r2, mul_pow, mul_pow, r4, r6, r3]
    rw [zexp, ← r5, ← r7a]
    ring
  have hmain : (1 : ℝ)
      ≤ (H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
          * ((((m : ℝ) * H) / T) ^ (m - 1))) ^ s
        * (H ^ (2 * L * (m : ℝ) * (d : ℝ))
          * Real.exp (2 * L * (m : ℝ) * H ^ 2) * (L ^ 2 * X) ^ d) :=
    hLo.trans (hsub.trans hreg.le)
  have hQ := gs_arith_Q hH hL1 hd hsM h2Lm hX0 hLX
  have hB := gs_arith_ZY hH hT hd hm hL
  have hZ1nn : (0 : ℝ) ≤ H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
      * ((((m : ℝ) * H) / T) ^ (m - 1)) := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact mul_nonneg hH0 hL0
        · exact le_of_lt (Real.exp_pos _)
      · exact pow_nonneg h2LH0 _
    · exact pow_nonneg (div_nonneg (mul_nonneg hmR0 hH0) hT0) _
  have hYnn : (0 : ℝ)
      ≤ H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg hH0 _
      · exact le_of_lt (Real.exp_pos _)
    · exact pow_nonneg h2L0 _
  have hZYnn : (0 : ℝ) ≤ (H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
      * ((((m : ℝ) * H) / T) ^ (m - 1)))
      * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) :=
    mul_nonneg hZ1nn hYnn
  have hZYlt1 : (H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
      * ((((m : ℝ) * H) / T) ^ (m - 1)))
      * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) < 1 :=
    lt_of_le_of_lt hB ((div_lt_one hT).mpr hK)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero] at hsM
    linarith [hM4]
  have hQle : H ^ (2 * L * (m : ℝ) * (d : ℝ))
        * Real.exp (2 * L * (m : ℝ) * H ^ 2) * (L ^ 2 * X) ^ d
      ≤ (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ s :=
    hQ.1.trans hQ.2
  have hle : (H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
        * ((((m : ℝ) * H) / T) ^ (m - 1))) ^ s
        * (H ^ (2 * L * (m : ℝ) * (d : ℝ))
          * Real.exp (2 * L * (m : ℝ) * H ^ 2) * (L ^ 2 * X) ^ d)
      ≤ (H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
        * ((((m : ℝ) * H) / T) ^ (m - 1))) ^ s
        * ((H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d)) ^ s) :=
    mul_le_mul_of_nonneg_left hQle (pow_nonneg hZ1nn s)
  rw [← mul_pow] at hle
  have hcontra1 : (1 : ℝ) ≤ ((H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
      * ((((m : ℝ) * H) / T) ^ (m - 1)))
      * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d))) ^ s :=
    hmain.trans hle
  have hcontra2 : ((H * L * Real.exp (2 * H) * (2 * L * H) ^ (d - 1)
      * ((((m : ℝ) * H) / T) ^ (m - 1)))
      * (H ^ (4 * d) * Real.exp (H ^ 2) * (2 * L) ^ (2 * d))) ^ s < 1 :=
    pow_lt_one₀ hZYnn hZYlt1 hs0
  linarith [hcontra1, hcontra2]

end GS_ARITH

/-- The number field generated by the three values. -/
private noncomputable abbrev gs_K (a b c : ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({a, b, c} : Set ℂ)

/--
The every-value complex form of Gelfond–Schneider. If `a` and `b` are algebraic, `a ≠ 1`,
`b` is not rational, and `z` is any logarithm of `a`, then `exp (b * z)` is transcendental.
The hypothesis `exp z = a` already implies `a ≠ 0`. Taking
`z = log a + n * (2 * π * I)` recovers every integer-indexed logarithm branch.

Source: A. O. Gelfond, *Sur le septième problème de Hilbert* (1934), and T. Schneider,
*Transzendenzuntersuchungen periodischer Funktionen I. Transzendenz von Potenzen*, J. Reine
Angew. Math. 172 (1935), 65–69, DOI 10.1515/crll.1935.172.65. Explicit arbitrary- and
principal-branch applications occur in arXiv:2311.11127v1, arXiv:2607.23662v1, and
arXiv:2608.17545v1. The Lean formalization in arXiv:2603.24823v1 states only the principal
`Complex.cpow` value; this declaration records the arbitrary-logarithm form.

Proves `Wanted` entry `gelfondSchneider_complex_exp`.
-/
theorem gelfondSchneider_complex_exp :
    ∀ {a b z : ℂ}, IsAlgebraic ℚ a → IsAlgebraic ℚ b → a ≠ 1 →
      b ∉ Set.range (algebraMap ℚ ℂ) → Complex.exp z = a →
        Transcendental ℚ (Complex.exp (b * z)) := by
  intro a b z ha hb ha1 hbrat hz
  classical
  unfold Transcendental
  intro hc
  set c : ℂ := Complex.exp (b * z) with hcdef
  have hℓ : z ≠ 0 := by
    intro h0
    apply ha1
    rw [← hz, h0, Complex.exp_zero]
  have : NumberField (gs_K a b c) := gs_numberField a b c ha hb hc
  obtain ⟨δ, hδpos, α', β', γ', hα, hβ, hγ⟩ :=
    gs_clear_denominators a b c ha hb hc
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ (α β : Type) [Fintype α] [Fintype β]
      (ma : Matrix α β (NumberField.RingOfIntegers (gs_K a b c))),
      ma ≠ 0 → ∀ (p q : ℕ), 0 < p → p < q → Fintype.card β = q → ∀ (A : ℝ),
        (∀ k l, NumberField.house
          (algebraMap (NumberField.RingOfIntegers (gs_K a b c))
            (gs_K a b c) (ma k l)) ≤ A) →
          Fintype.card α = p →
          ∃ ξ : β → NumberField.RingOfIntegers (gs_K a b c), ξ ≠ 0 ∧
            ma.mulVec ξ = 0 ∧
            ∀ l, NumberField.house ((ξ l) : (gs_K a b c)) ≤
              C₀ * (C₀ * q * A) ^ ((p : ℝ) / (q - p)) :=
    gs_siegel_exist (gs_K a b c)
  set d : ℕ := Module.finrank ℚ (gs_K a b c) with hddef
  have hd_pos : 0 < d := gs_finrank_pos a b c ha hb hc
  have hd1 : 1 ≤ d := by omega
  have h1δ : 1 ≤ δ := by omega
  set H : ℝ :=
    max 1 (max (δ : ℝ) (max (NumberField.house (α' : gs_K a b c))
      (max (NumberField.house (β' : gs_K a b c))
      (max (NumberField.house (γ' : gs_K a b c))
      (max ‖z‖ (max ‖b‖ (C₀ ^ 2))))))) with hHdef
  have hH : 1 ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inl le_rfl
  have hδH : (δ : ℝ) ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inr (Or.inl le_rfl)
  have hHα : NumberField.house
      ((α' : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c)) ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inr (Or.inr (Or.inl le_rfl))
  have hHβ : NumberField.house
      ((β' : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c)) ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inl le_rfl)))
  have hHγ : NumberField.house
      ((γ' : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c)) ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl le_rfl))))
  have hzH : ‖z‖ ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl le_rfl)))))
  have hbH : ‖b‖ ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl le_rfl))))))
  have hC₂ : C₀ ^ 2 ≤ H := by
    rw [hHdef]
    simp only [le_max_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr le_rfl))))))
  -- The sample count, threshold, grid sizes and bounds.
  set m : ℕ := 3 * d + 2 with hmdef
  set K₀ : ℝ := H ^ (5 * d) * Real.exp (2 * H + H ^ 2) * (4 * (m : ℝ)) ^ (3 * d)
    * (((m : ℝ) * H) ^ (3 * d + 1)) with hK0def
  set T : ℕ := ⌈K₀⌉₊ + 1 with hTdef
  set L : ℕ := 2 * m * T with hLdef
  set M : ℕ := 2 * m * T ^ 2 with hMdef
  set E : ℕ := M + 2 * (L * m) with hEdef
  set A : ℝ := H ^ E * (2 * (L : ℝ)) ^ M with hAdef
  set X : ℝ := H * (L : ℝ) ^ 2 * A with hXdef
  have hK0le : K₀ ≤ ((⌈K₀⌉₊ : ℕ) : ℝ) := by rw [← Nat.ceil_le]
  have hKT : K₀ < (T : ℝ) := by
    rw [hTdef]
    push_cast
    exact lt_of_le_of_lt hK0le (by exact_mod_cast Nat.lt_succ_self _)
  have hT0 : 0 < T := by
    rw [hTdef]
    omega
  have hm0 : 0 < m := by
    rw [hmdef]
    omega
  have h1m : 1 ≤ m := by omega
  have hL0 : 0 < L := by
    rw [hLdef]
    positivity
  have h1L : 1 ≤ L := by omega
  have hM0 : 0 < M := by
    rw [hMdef]
    positivity
  have h1M : 1 ≤ M := by omega
  have hp : 0 < M * m := Nat.mul_pos hM0 hm0
  have hq : L * L = 2 * (M * m) := by
    rw [hLdef, hMdef]
    ring
  have hMT : M = L * T := by
    rw [hMdef, hLdef]
    ring
  have hE : ∀ (k n : ℕ) (t : Fin (L * L)), k < M → n ≤ m →
      k + ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n +
        ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n ≤ E := by
    intro k n t hkM hnm
    rw [hEdef]
    have hi : ((finProdFinEquiv (m := L) (n := L)).symm t).1.val ≤ L :=
      Nat.le_of_lt (Fin.is_lt _)
    have hj : ((finProdFinEquiv (m := L) (n := L)).symm t).2.val ≤ L :=
      Nat.le_of_lt (Fin.is_lt _)
    have h1 : ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n ≤ L * m :=
      Nat.mul_le_mul hi hnm
    have h2 : ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n ≤ L * m :=
      Nat.mul_le_mul hj hnm
    omega
  have haK : algebraMap (gs_K a b c) ℂ ⟨a, gs_mem_adjoin_a a b c⟩ = a := by simp
  have hbK : algebraMap (gs_K a b c) ℂ ⟨b, gs_mem_adjoin_b a b c⟩ = b := by simp
  have hcK : algebraMap (gs_K a b c) ℂ ⟨c, gs_mem_adjoin_c a b c⟩ = c := by simp
  have hℓc : Complex.exp (b * z) = c := by rw [hcdef]
  obtain ⟨ξ, hξne, hξb, hvan⟩ := gs_aux_function (gs_K a b c)
    haK hbK hcK hz hℓc hα hβ hγ h1δ C₀ hC₂ hC₀ hH hδH hHα hHβ hHγ
    h1L h1m h1M hE hAdef hXdef hq hp
  set F : ℂ → ℂ := fun w : ℂ => ∑ t : Fin (L * L),
    (algebraMap (gs_K a b c) ℂ)
      (((ξ t : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c))) *
      Complex.exp (gs_ω b L t * w) with hFdef
  have hvanF : ∀ (k n : ℕ), k < M → 1 ≤ n → n ≤ m →
      iteratedDeriv k F ((n : ℂ) * z) = 0 :=
    fun k n hk hn1 hnm => hvan k n hk hn1 hnm
  have hu12 : ∀ t : Fin (L * L),
      ‖(algebraMap (gs_K a b c) ℂ)
        (((ξ t : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c)))‖ ≤
        X := by
    intro t
    exact (NumberField.norm_embedding_le_house _ _).trans (hξb t)
  -- The frequency map is injective, and the coefficient function is nonzero.
  have hinj : Function.Injective (gs_ω b L) := gs_freq_injective b hbrat L
  have hu0 : (fun t : Fin (L * L) => (algebraMap (gs_K a b c) ℂ)
      (((ξ t : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c)))) ≠
      0 := by
    obtain ⟨t₀, ht₀⟩ := Function.ne_iff.mp hξne
    intro hcon
    apply ht₀
    have ht : (algebraMap (gs_K a b c) ℂ)
        (((ξ t₀ : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c))) =
        0 := congrFun hcon t₀
    have hinjι : Function.Injective (algebraMap (gs_K a b c) ℂ) :=
      RingHom.injective _
    have hK0 : (((ξ t₀ : NumberField.RingOfIntegers (gs_K a b c)) :
        (gs_K a b c))) = 0 := hinjι (by rw [map_zero]; exact ht)
    have h00 : ξ t₀ = 0 :=
      NumberField.RingOfIntegers.coe_injective (by rw [map_zero]; exact hK0)
    exact h00
  -- Some derivative at the first sample point is nonzero; take the least order.
  obtain ⟨k, hk⟩ := gs_zero_estimate hinj hu0 z
  have hFlam : F = fun w : ℂ => ∑ t : Fin (L * L),
      (algebraMap (gs_K a b c) ℂ)
        (((ξ t : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c))) *
        Complex.exp (gs_ω b L t * w) := rfl
  have hkv : iteratedDeriv k.val F (((1 : ℕ) : ℂ) * z) ≠ 0 := by
    rw [hFlam, gs_iteratedDeriv_expSum]
    simp only [Nat.cast_one, one_mul]
    exact hk
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, h1m⟩
  have hex : ∃ kk : ℕ, ∃ n ∈ Finset.Icc 1 m,
      iteratedDeriv kk F ((n : ℂ) * z) ≠ 0 :=
    ⟨k.val, 1, h1mem, hkv⟩
  obtain ⟨n₀, hn₀mem, hsne⟩ := Nat.find_spec hex
  set s : ℕ := Nat.find hex with hsdef
  have hn₀1 : 1 ≤ n₀ := (Finset.mem_Icc.mp hn₀mem).1
  have hn₀m : n₀ ≤ m := (Finset.mem_Icc.mp hn₀mem).2
  have hmin : ∀ (n kk : ℕ), 1 ≤ n → n ≤ m → kk < s →
      iteratedDeriv kk F ((n : ℂ) * z) = 0 := by
    intro n kk hn1 hnm hks
    by_contra hne'
    have hmem : n ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hn1, hnm⟩
    have hle : s ≤ kk := Nat.find_min' hex ⟨n, hmem, hne'⟩
    omega
  have hsM : M ≤ s := by
    by_contra hlt
    push Not at hlt
    exact hsne (hvanF s n₀ hlt hn₀1 hn₀m)
  -- The coefficient bound is at least one.
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1L
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ hH
    · apply one_le_pow₀
      have hLp : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
      linarith
  have h1X : 1 ≤ X := by
    rw [hXdef]
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le hH
      exact one_le_pow₀ hLR
    · exact hA1
  have hF12 : ∀ w : ℂ, F w = ∑ t : Fin (L * L),
      (algebraMap (gs_K a b c) ℂ)
        (((ξ t : NumberField.RingOfIntegers (gs_K a b c)) : (gs_K a b c))) *
        Complex.exp (gs_ω b L t * w) := fun w => rfl
  -- The threshold exceeds `m * H`.
  have hmH1 : (1 : ℝ) ≤ (m : ℝ) * H :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast h1m) hH
  have hm5 : 5 ≤ m := by omega
  have hD : (m : ℝ) * H ≤ ((m : ℝ) * H) ^ (3 * d + 1) :=
    le_self_pow₀ hmH1 (by omega)
  have hA1K : (1 : ℝ) ≤ H ^ (5 * d) := one_le_pow₀ hH
  have hB1K : (1 : ℝ) ≤ Real.exp (2 * H + H ^ 2) :=
    Real.one_le_exp (by linarith [sq_nonneg H])
  have hC1K : (1 : ℝ) ≤ (4 * (m : ℝ)) ^ (3 * d) := by
    apply one_le_pow₀
    have h5 : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm5
    linarith
  have hmH : (m : ℝ) * H ≤ K₀ := by
    rw [hK0def]
    apply le_trans hD
    have hABC : (1 : ℝ) ≤ H ^ (5 * d) * Real.exp (2 * H + H ^ 2)
        * (4 * (m : ℝ)) ^ (3 * d) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hA1K hB1K) hC1K
    have hD0 : (0 : ℝ) ≤ ((m : ℝ) * H) ^ (3 * d + 1) :=
      pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) _
    exact le_mul_of_one_le_left hD0 hABC
  have hTmH : (m : ℝ) * H < (T : ℝ) := lt_of_le_of_lt hmH hKT
  -- The upper bound, the lower bound, and the final arithmetic contradiction.
  have hUpper := gs_upper_bound hbrat hℓ hF12 hu12 hu0 h1X hH hzH hbH
    h1L h1m hn₀1 hn₀m hsM hMT hTmH hmin hsne
  have hLower := gs_lower_bound (gs_K a b c) haK hbK hcK hz hℓc hα hβ hγ
    hddef.symm hH hδH h1δ hHα hHβ hHγ hξb hn₀m hF12 hsne
  have hK := hKT
  rw [hK0def] at hK
  have hL : ((L : ℕ) : ℝ) = 2 * (m : ℝ) * (T : ℝ) := by simp [hLdef]
  have hM : ((M : ℕ) : ℝ) = 2 * (m : ℝ) * (T : ℝ) ^ 2 := by simp [hMdef]
  have hsMr : (M : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsM
  have hXr : X = H * (L : ℝ) ^ 2 * H ^ ((M : ℝ) + 2 * (L : ℝ) * (m : ℝ)) *
      (2 * (L : ℝ)) ^ ((M : ℝ)) := by
    rw [hXdef, hAdef]
    have hEcast : ((E : ℕ) : ℝ) = (M : ℝ) + 2 * (L : ℝ) * (m : ℝ) := by
      rw [hEdef]
      push_cast
      ring
    rw [← hEcast, ← Real.rpow_natCast H E, ← Real.rpow_natCast (2 * (L : ℝ)) M]
    ring
  have hU : ‖iteratedDeriv s F ((n₀ : ℂ) * z)‖ ≤ (L : ℝ) ^ s *
      ((L : ℝ) ^ 2 * X * Real.exp (2 * H * (s : ℝ) + 2 * (L : ℝ) * (m : ℝ) *
        H ^ 2)) *
      ((((m : ℝ) * H / (T : ℝ)) ^ (s * (m - 1)))) := hUpper
  have hLo : 1 ≤ H ^ ((s : ℝ) + 2 * (L : ℝ) * (m : ℝ)) *
      ‖iteratedDeriv s F ((n₀ : ℂ) * z)‖ *
      (((L : ℝ) ^ 2 * X * H ^ (2 * (L : ℝ) * (m : ℝ)) *
        (2 * (L : ℝ) * H) ^ s)) ^ (d - 1) := hLower
  exact gs_arith_final hH hd1 hmdef hK hL hM hsMr hXr hU hLo

/--
`Real.rpow` specialization of Gelfond–Schneider: if `α β : ℝ` satisfy `0 < α`, `α ≠ 1`,
`IsAlgebraic ℚ α`, `IsAlgebraic ℚ β` and `Irrational β`, then `Real.rpow α β` is transcendental
over `ℚ`. Source: A. O. Gelfond, Sur le septième problème de Hilbert, Dokl. Akad. Nauk SSSR 2
(1934) 1–6 and T. Schneider 1935 independent; textbook in Baker, Transcendental Number Theory

Proves `Wanted` entry `gelfondSchneider_real_rpow`.
-/
theorem gelfondSchneider_real_rpow :
    ∀ (α β : ℝ), 0 < α → α ≠ 1 → IsAlgebraic ℚ α → IsAlgebraic ℚ β →
      Irrational β → Transcendental ℚ (Real.rpow α β) := by
  intro α β hpos hne ha hb hirr
  unfold Transcendental
  intro halg
  -- Transfer algebraicity along `ℝ → ℂ`.
  have hcoeinj : Function.Injective (algebraMap ℝ ℂ) := by
    rw [RCLike.algebraMap_eq_ofReal]
    exact RCLike.ofReal_injective
  have h1 : IsAlgebraic ℚ ((α : ℝ) : ℂ) := by
    have h := (isAlgebraic_algebraMap_iff hcoeinj).mpr ha
    rwa [RCLike.algebraMap_eq_ofReal] at h
  have h2 : IsAlgebraic ℚ ((β : ℝ) : ℂ) := by
    have h := (isAlgebraic_algebraMap_iff hcoeinj).mpr hb
    rwa [RCLike.algebraMap_eq_ofReal] at h
  have h3 : ((α : ℝ) : ℂ) ≠ 1 := by
    intro hcon
    apply hne
    have h4 : ((α : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [hcon, Complex.ofReal_one]
    exact Complex.ofReal_injective h4
  have h4 : ((β : ℝ) : ℂ) ∉ Set.range (algebraMap ℚ ℂ) := by
    intro hmem
    obtain ⟨q, hq⟩ := hmem
    have e : ((β : ℝ) : ℂ) = ((q : ℚ) : ℂ) := by
      rw [← hq]
      exact eq_ratCast _ _
    exact hirr.ne_rat q (Complex.ofReal_injective e)
  have h5 : Complex.exp (((Real.log α : ℝ)) : ℂ) = ((α : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hpos]
  have h0 : Real.rpow α β = Real.exp (Real.log α * β) :=
    Real.rpow_def_of_pos hpos β
  have hexp : Complex.exp (((β : ℝ) : ℂ) * (((Real.log α : ℝ)) : ℂ))
      = ((Real.rpow α β : ℝ) : ℂ) := by
    conv_rhs => rw [h0]
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
    congr 1
    ring
  have halgC : IsAlgebraic ℚ ((Real.rpow α β : ℝ) : ℂ) := by
    have h := (isAlgebraic_algebraMap_iff hcoeinj).mpr halg
    rwa [RCLike.algebraMap_eq_ofReal] at h
  have hcon : Transcendental ℚ
      (Complex.exp (((β : ℝ) : ℂ) * (((Real.log α : ℝ)) : ℂ))) :=
    gelfondSchneider_complex_exp h1 h2 h3 h4 h5
  rw [hexp] at hcon
  exact hcon halgC

end MathlibExt.NumberTheory.TranscendenceWanted

end
