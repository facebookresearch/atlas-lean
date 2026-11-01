/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import MathlibExt.Analysis.Complex.HadamardFactorization
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import MathlibExt.Analysis.Complex.PhragmenLindelofStrip
import MathlibExt.Analysis.Complex.RectangleArgumentPrinciple
import MathlibExt.Analysis.SpecialFunctions.Gamma.Vertical
import MathlibExt.Analysis.SpecialFunctions.Gamma.Binet
import MathlibExt.NumberTheory.SelbergClass.CompletedFunction
import MathlibExt.NumberTheory.SelbergClass.DegreeZero
import MathlibExt.NumberTheory.SelbergClass.Growth

/-!
# Counting the zeros of a function in the Selberg class

**Selberg's zero-counting theorem.** Let `a` be in the Selberg class with continuation `F` and a
functional equation of degree `d`. The number `N(T)` of zeros `ρ` of `F` with `Re ρ ≥ 0` and
`0 ≤ Im ρ ≤ T`, counted with multiplicity, satisfies `N(T) ∼ (d / 2π) T log T` as `T → ∞`.

The proof applies the argument principle to the completed function
`H(s) = s^m Q^s ∏ Γ(α_i s + r_i) (s - 1)^m F(s)` on a rectangle symmetric under `s ↦ 1 - s̄`,
folds it in half with the functional equation, evaluates the archimedean part with Stirling's
formula for the digamma function, and bounds the change of argument of `F` on the top edge by
Backlund's argument and Jensen's formula. For degree `0` the function is `1` (Conrey–Ghosh) and
`N(T) = 0`.

## Main statements

* `SelbergClass.isEquivalent_zeroCount`: Selberg's zero-counting theorem.
-/

open ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClass

private lemma zeroCount_eq_zero_of_degree_eq_zero (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass)
    (F : ℂ → ℂ)
    (hF : IsLSeriesContinuation a F) (D : FunctionalEquation F) (hD : D.degree = 0) (T : ℝ) :
    (∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T}, analyticOrderNatAt F ρ) = 0 := by
  have ha1 := eq_one_of_degree_eq_zero ha hF D hD
  subst ha1
  have hF1 : ∀ s : ℂ, s ≠ 1 → F s = 1 := by
    have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have h3 : F =ᶠ[nhds (2 : ℂ)] fun _ => (1 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
      rw [hF.1 s hs]
      have : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
        funext n
        simp [ArithmeticFunction.one_apply, LSeries.delta]
      rw [this, LSeries_delta]
      rfl
    intro s hs
    exact (hF.2.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const) hpc (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) h3 hs
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro ρ hρ
  have hρ1 : ρ = 1 := by
    by_contra h
    have := hρ.1
    rw [hF1 ρ h] at this
    exact one_ne_zero this
  subst hρ1
  have hna : ¬ AnalyticAt ℂ F 1 := by
    intro han
    have hc := han.continuousAt
    have hlim : Filter.Tendsto F (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
      apply tendsto_nhdsWithin_congr (f := fun _ => (1 : ℂ))
      · intro s hs; exact (hF1 s hs).symm
      · exact tendsto_const_nhds.mono_left nhdsWithin_le_nhds
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    have := tendsto_nhds_unique h2 hlim
    rw [hρ.1] at this
    exact zero_ne_one this
  simp [analyticOrderNatAt, analyticOrderAt, hna]

open Metric in
/-- Jensen: the real zeros of `g` in `[c - r, c + r]` lie in a finite set of size at most
`log (M / |g c|) / log (R / r)`. -/
private lemma exists_finset_real_zeros_card_le_of_jensen (g : ℂ → ℂ) (c r R M : ℝ) (hr : 0 < r) (hrR
    : r < R)
    (hM : 1 ≤ M) (hg : AnalyticOnNhd ℂ g (closedBall (c : ℂ) R)) (hgc : g c ≠ 0)
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖g z‖ ≤ M) :
    ∃ Zs : Finset ℝ, (Zs.card : ℝ) ≤ Real.log (M / ‖g c‖) / Real.log (R / r) ∧
      ∀ x : ℝ, |x - c| ≤ r → g x = 0 → x ∈ Zs := by
  have hR : 0 < R := by linarith
  have hJ := AnalyticOnNhd.sum_divisor_le (c := (c : ℂ)) (r := r) (R := R) (M := M)
    (by rw [abs_of_pos hr]; exact hr) (by rw [abs_of_pos hr, abs_of_pos hR]; exact hrR) hM
    (by rw [abs_of_pos hR]; exact hg) hgc (by rw [abs_of_pos hR]; exact hbound)
  rw [abs_of_pos hr] at hJ
  set D := MeromorphicOn.divisor g (closedBall (c : ℂ) r) with hD
  have hgr : AnalyticOnNhd ℂ g (closedBall (c : ℂ) r) :=
    hg.mono (closedBall_subset_closedBall hrR.le)
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  set Zc := hfin.toFinset with hZc
  refine ⟨Zc.image Complex.re, ?_, ?_⟩
  · have hnn : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hgr u
    have h1 : ((Zc.image Complex.re).card : ℝ) ≤ Zc.card := by
      exact_mod_cast Finset.card_image_le
    have h2 : (Zc.card : ℤ) ≤ ∑ u ∈ Zc, D u := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun u hu => ?_
      rw [hZc, Set.Finite.mem_toFinset, Function.mem_support] at hu
      have := hnn u
      push_cast
      omega
    have h3 : ∑ u ∈ Zc, D u = ∑ᶠ u, D u :=
      (finsum_eq_sum_of_support_subset D (by rw [hZc, Set.Finite.coe_toFinset])).symm
    have h4 : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ Real.log (M / ‖g c‖) / Real.log (R / r) := hJ
    have h2' : (Zc.card : ℝ) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by
      rw [← h3]; exact_mod_cast h2
    linarith
  · intro x hx hgx
    have hmem : (x : ℂ) ∈ closedBall (c : ℂ) r := by
      rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact hx
    have hDx : D x ≠ 0 := by
      rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hgr hmem]
      have hfin' : analyticOrderAt g x ≠ ⊤ := by
        refine hg.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall _ _).isPreconnected
          (mem_closedBall_self hR.le) (closedBall_subset_closedBall hrR.le hmem) ?_
        rw [Ne, analyticOrderAt_eq_top]
        intro h
        exact hgc h.self_of_nhds
      have hpos : analyticOrderAt g x ≠ 0 := by
        rw [Ne, (hgr x hmem).analyticOrderAt_eq_zero]
        exact not_not.2 hgx
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin'
      rw [← hn] at hpos ⊢
      simp only [ENat.map_natCast, WithTop.untop₀_coe]
      exact_mod_cast (by simpa using hpos : n ≠ 0)
    have hxZ : (x : ℂ) ∈ Zc := by
      rw [hZc, Set.Finite.mem_toFinset, Function.mem_support]
      exact hDx
    exact Finset.mem_image.2 ⟨x, hxZ, by simp⟩

open Complex Set in
/-- On an arc where `Re φ > 0` in the interior, the argument change of `φ` is at most `π`. -/
private lemma abs_im_integral_logDeriv_le_pi_of_re_pos (φ φ' : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    (hne : ∀ x ∈ Icc a b, φ x ≠ 0) (hpos : ∀ x ∈ Ioo a b, 0 < (φ x).re) :
    |(∫ x in a..b, φ' x / φ x).im| ≤ Real.pi := by
  have hcont : ∀ x ∈ Icc a b, ContinuousAt φ x := fun x hx => (hd x hx).continuousAt
  have hend : ∀ x ∈ Icc a b, 0 ≤ (φ x).re := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have hev : ∀ᶠ y in nhds x, (φ y).re < 0 :=
      ((Complex.continuous_re.continuousAt).comp (hcont x hx)).eventually
        (gt_mem_nhds hneg)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    rcases eq_or_lt_of_le hx.1 with hxa | hxa
    · set y := x + min (ε / 2) ((b - x) / 2) with hy
      have h1 : 0 < min (ε / 2) ((b - x) / 2) := lt_min (by linarith) (by linarith [hab, hxa])
      have h2 : min (ε / 2) ((b - x) / 2) ≤ ε / 2 := min_le_left _ _
      have h3 : min (ε / 2) ((b - x) / 2) ≤ (b - x) / 2 := min_le_right _ _
      have hyd : dist y x < ε := by
        rw [Real.dist_eq, hy, add_sub_cancel_left, abs_of_pos h1]; linarith
      have := hball hyd
      have := hpos y ⟨by linarith, by linarith⟩
      linarith
    · set y := x - min (ε / 2) ((x - a) / 2) with hy
      have h1 : 0 < min (ε / 2) ((x - a) / 2) := lt_min (by linarith) (by linarith)
      have h2 : min (ε / 2) ((x - a) / 2) ≤ ε / 2 := min_le_left _ _
      have h3 : min (ε / 2) ((x - a) / 2) ≤ (x - a) / 2 := min_le_right _ _
      have hyd : dist y x < ε := by
        rw [Real.dist_eq, hy, sub_sub_cancel_left, abs_neg, abs_of_pos h1]; linarith
      have := hball hyd
      have := hpos y ⟨by linarith, by linarith [hx.2]⟩
      linarith
  have hslit : ∀ x ∈ Icc a b, φ x ∈ slitPlane := by
    intro x hx
    rw [mem_slitPlane_iff]
    rcases eq_or_lt_of_le (hend x hx) with h | h
    · right
      intro him
      exact hne x hx (Complex.ext h.symm him)
    · left; exact h
  have hint : IntervalIntegrable (fun x => φ' x / φ x) MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab.le]
    exact hc.div (fun x hx => (hcont x hx).continuousWithinAt) hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Complex.log (φ x))
    (fun x hx => by
      rw [uIcc_of_le hab.le] at hx
      exact (hd x hx).clog_real (hslit x hx)) hint]
  rw [Complex.sub_im, Complex.log_im, Complex.log_im]
  have ha := Complex.abs_arg_le_pi_div_two_iff.2 (hend a ⟨le_refl a, hab.le⟩)
  have hb := Complex.abs_arg_le_pi_div_two_iff.2 (hend b ⟨hab.le, le_refl b⟩)
  rw [abs_le] at ha hb ⊢
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

open Complex Set in
/-- On an arc where `Re φ ≠ 0` in the interior, the argument change of `φ` is at most `π`. -/
private lemma abs_im_integral_logDeriv_le_pi_of_re_ne_zero (φ φ' : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    (hne : ∀ x ∈ Icc a b, φ x ≠ 0) (hre : ∀ x ∈ Ioo a b, (φ x).re ≠ 0) :
    |(∫ x in a..b, φ' x / φ x).im| ≤ Real.pi := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [Real.pi_pos.le]
  have hcre : ContinuousOn (fun x => (φ x).re) (Icc a b) := fun x hx =>
    (Complex.continuous_re.continuousAt.comp (hd x hx).continuousAt).continuousWithinAt
  have hsign : (∀ x ∈ Ioo a b, 0 < (φ x).re) ∨ (∀ x ∈ Ioo a b, (φ x).re < 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩ := hcon
    have h1' : (φ x1).re < 0 := lt_of_le_of_ne h1 (hre x1 hx1)
    have h2' : 0 < (φ x2).re := lt_of_le_of_ne h2 (Ne.symm (hre x2 hx2))
    have hsub : uIcc x1 x2 ⊆ Ioo a b := (ordConnected_Ioo).uIcc_subset hx1 hx2
    have hcon' : ContinuousOn (fun x => (φ x).re) (uIcc x1 x2) :=
      hcre.mono (hsub.trans Ioo_subset_Icc_self)
    obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hcon'
      (show (0 : ℝ) ∈ uIcc (φ x1).re (φ x2).re from by
        rw [mem_uIcc]; left; exact ⟨h1'.le, h2'.le⟩)
    exact hre x (hsub hx) hx0
  rcases hsign with hpos | hneg
  · exact abs_im_integral_logDeriv_le_pi_of_re_pos φ φ' a b hlt hd hc hne hpos
  · have := abs_im_integral_logDeriv_le_pi_of_re_pos (fun x => -φ x) (fun x => -φ' x) a b hlt (fun x
      hx => (hd x hx).neg)
      hc.neg (fun x hx => neg_ne_zero.2 (hne x hx)) (fun x hx => by
        simp only [Complex.neg_re]; linarith [hneg x hx])
    simpa only [neg_div_neg_eq] using this

open Complex Set in
/-- **Backlund's bound.** If `Re φ` has its zeros in the open interval `(a, b)` inside a finite
set `Z`, the argument change of `φ` over `[a, b]` is at most `(#Z + 1) π`. -/
private lemma abs_im_integral_logDeriv_le_of_re_zeros (φ φ' : ℝ → ℂ) (a0 b0 : ℝ)
    (hd : ∀ x ∈ Icc a0 b0, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a0 b0))
    (hne : ∀ x ∈ Icc a0 b0, φ x ≠ 0) (Z : Finset ℝ) :
    ∀ n : ℕ, ∀ a b : ℝ, a0 ≤ a → a ≤ b → b ≤ b0 →
      (Z.filter (fun x => x ∈ Ioo a b)).card = n →
      (∀ x ∈ Ioo a b, (φ x).re = 0 → x ∈ Z) →
      |(∫ x in a..b, φ' x / φ x).im| ≤ (n + 1) * Real.pi := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b ha hab hb hcard hZ
  have hsub : Icc a b ⊆ Icc a0 b0 := Icc_subset_Icc ha hb
  by_cases hex : ∃ x0 ∈ Ioo a b, (φ x0).re = 0
  · obtain ⟨x0, hx0, hx00⟩ := hex
    have hx0Z := hZ x0 hx0 hx00
    set Z1 := Z.filter (fun x => x ∈ Ioo a x0)
    set Z2 := Z.filter (fun x => x ∈ Ioo x0 b)
    have hdisj : Disjoint Z1 Z2 := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Z1, Z2, Finset.mem_filter, mem_Ioo] at h1 h2
      linarith [h1.2.2, h2.2.1]
    have hx0n : x0 ∉ Z1 ∪ Z2 := by
      simp [Z1, Z2]
    have hsubset : insert x0 (Z1 ∪ Z2) ⊆ Z.filter (fun x => x ∈ Ioo a b) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_union, Z1, Z2, Finset.mem_filter, mem_Ioo] at hx
      simp only [Finset.mem_filter, mem_Ioo]
      rcases hx with rfl | ⟨hx, h1, h2⟩ | ⟨hx, h1, h2⟩
      · exact ⟨hx0Z, hx0⟩
      · exact ⟨hx, h1, by linarith [hx0.2]⟩
      · exact ⟨hx, by linarith [hx0.1], h2⟩
    have hc12 := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hx0n, Finset.card_union_of_disjoint hdisj, hcard] at hc12
    have h1 := ih Z1.card (by omega) a x0 ha hx0.1.le (by linarith [hx0.2]) rfl (fun x hx hx0' =>
      hZ x ⟨hx.1, by linarith [hx.2, hx0.2]⟩ hx0')
    have h2 := ih Z2.card (by omega) x0 b (by linarith [hx0.1]) hx0.2.le hb rfl (fun x hx hx0' =>
      hZ x ⟨by linarith [hx.1, hx0.1], hx.2⟩ hx0')
    have hint : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
        IntervalIntegrable (fun x => φ' x / φ x) MeasureTheory.volume u v := by
      intro u v hu huv hv
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le huv]
      have hs : Icc u v ⊆ Icc a0 b0 := (Icc_subset_Icc hu hv).trans hsub
      exact (hc.mono hs).div (fun x hx => (hd x (hs hx)).continuousAt.continuousWithinAt)
        (fun x hx => hne x (hs hx))
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint a x0 le_rfl hx0.1.le hx0.2.le) (hint x0 b hx0.1.le hx0.2.le le_rfl), Complex.add_im]
    have hpi := Real.pi_pos
    calc |(∫ x in a..x0, φ' x / φ x).im + (∫ x in x0..b, φ' x / φ x).im|
        ≤ |(∫ x in a..x0, φ' x / φ x).im| + |(∫ x in x0..b, φ' x / φ x).im| := abs_add_le _ _
      _ ≤ (Z1.card + 1) * Real.pi + (Z2.card + 1) * Real.pi := add_le_add h1 h2
      _ ≤ (n + 1) * Real.pi := by
        have : ((Z1.card : ℝ) + 1) + (Z2.card + 1) ≤ n + 1 := by exact_mod_cast (by omega)
        nlinarith
  · push Not at hex
    have := abs_im_integral_logDeriv_le_pi_of_re_ne_zero φ φ' a b hab (fun x hx => hd x (hsub hx))
        (hc.mono hsub)
      (fun x hx => hne x (hsub hx)) hex
    have hpi := Real.pi_pos
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

open Complex Metric in
/-- **The top edge.** At a height `B` where `F` has no zeros on `[1/2, σ1] + iB`, the argument
change of `F` along that segment is `O(log B)`: Backlund's bound plus Jensen. -/
private lemma exists_abs_im_integral_logDeriv_top_le_log (F : ℂ → ℂ) (hFd : DifferentiableOn ℂ F
    {1}ᶜ) (σ1 : ℝ) (hσ1 : 2 ≤ σ1)
    (hnear : ∀ s : ℂ, σ1 ≤ s.re → ‖F s - 1‖ ≤ 1 / 2) (A C : ℝ) (hA : 0 ≤ A)
    (hgrow : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 * σ1 → 1 ≤ |s.im| → ‖F s‖ ≤ C * |s.im| ^ A) :
    ∃ K B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → (∀ x : ℝ, 1 / 2 ≤ x → x ≤ σ1 → F (x + B * I) ≠ 0) →
      |(∫ x in (1 / 2 : ℝ)..σ1, logDeriv F ((x : ℂ) + (B : ℂ) * I)).im| ≤ K * Real.log B := by
  set r : ℝ := σ1 - 1 / 2 with hr
  set R : ℝ := σ1 - 1 / 4 with hR
  have hr0 : 0 < r := by rw [hr]; linarith
  have hrR : r < R := by rw [hr, hR]; linarith
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr0]; exact hrR)
  set c₁ : ℝ := Real.log 2 + Real.log (1 + |C|) + A * Real.log 2 + A with hc₁
  refine ⟨(c₁ / Real.log (R / r) + 1) * Real.pi, σ1 + 3, fun B hB hne => ?_⟩
  have hB5 : 5 ≤ B := by linarith
  have hlogB : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  -- the auxiliary function
  set Fb : ℂ → ℂ := fun u => F (u + B * I) with hFb
  set g : ℂ → ℂ := fun z => (Fb z + starRingEnd ℂ (Fb (starRingEnd ℂ z))) / 2 with hg
  set U : Set ℂ := {z | |z.im| < B - 1} with hU
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hFbd : ∀ u : ℂ, |u.im| < B - 1 → DifferentiableAt ℂ Fb u := by
    intro u hu
    have hne1 : u + B * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      have := abs_lt.1 hu
      linarith
    exact (hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hne1)).comp u
      (differentiableAt_id.add_const _)
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hz' : |z.im| < B - 1 := hz
    have h1 := hFbd z hz'
    have h2 : DifferentiableAt ℂ (starRingEnd ℂ ∘ Fb ∘ starRingEnd ℂ) z :=
      differentiableAt_conj_conj_iff.mpr (hFbd _ (by simpa using hz'))
    exact ((h1.add h2).div_const 2).differentiableWithinAt
  have hga : AnalyticOnNhd ℂ g (closedBall (σ1 : ℂ) R) := by
    refine (hgd.analyticOnNhd hUo).mono fun z hz => ?_
    have := Complex.abs_im_le_norm (z - σ1)
    rw [mem_closedBall, dist_eq_norm] at hz
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    change |z.im| < B - 1
    linarith
  have hgreal : ∀ x : ℝ, g x = ((F (x + B * I)).re : ℂ) := by
    intro x
    simp only [hg, hFb, Complex.conj_ofReal]
    rw [Complex.add_conj]; push_cast; ring
  have hgσ : 1 / 2 ≤ ‖g σ1‖ := by
    rw [hgreal, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hnear (σ1 + B * I) (by simp)
    have h2 := Complex.re_le_norm (1 - F (σ1 + B * I))
    rw [norm_sub_rev] at h1
    simp only [Complex.sub_re, Complex.one_re] at h2
    rw [abs_of_pos (by linarith)]
    linarith
  set M : ℝ := (1 + |C|) * (2 * B) ^ A with hM
  have hM1 : 1 ≤ M := by
    have : 1 ≤ (2 * B) ^ A := Real.one_le_rpow (by linarith) hA
    have : 1 ≤ 1 + |C| := by have := abs_nonneg C; linarith
    nlinarith
  have hbound : ∀ z ∈ sphere (σ1 : ℂ) R, ‖g z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hre := Complex.abs_re_le_norm (z - σ1)
    have him := Complex.abs_im_le_norm (z - σ1)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at hre him
    rw [hz] at hre him
    have hre' := abs_le.1 hre
    have him' := abs_le.1 him
    have key : ∀ u : ℂ, u.re = z.re → |u.im| ≤ R → ‖F (u + B * I)‖ ≤ M := by
      intro u hu1 hu2
      have hu2' := abs_le.1 hu2
      have hui : (u + B * I).im = u.im + B := by simp
      have him1 : 1 ≤ |(u + B * I).im| := by
        rw [hui, abs_of_pos (by linarith)]; linarith
      have him2 : |(u + B * I).im| ≤ 2 * B := by
        rw [hui, abs_of_pos (by linarith)]; linarith
      have := hgrow (u + B * I) (by simp; linarith) (by simp; linarith) him1
      calc ‖F (u + B * I)‖ ≤ C * |(u + B * I).im| ^ A := this
        _ ≤ |C| * (2 * B) ^ A := by
          have h0 : 0 ≤ |(u + B * I).im| ^ A := by positivity
          calc C * |(u + B * I).im| ^ A ≤ |C| * |(u + B * I).im| ^ A := by
                gcongr; exact le_abs_self C
            _ ≤ |C| * (2 * B) ^ A := by gcongr
        _ ≤ M := by rw [hM]; nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ 2 * B by linarith) A]
    have h1 := key z rfl him
    have h2 := key (starRingEnd ℂ z) (by simp) (by simpa using him)
    simp only [hg, hFb]
    rw [norm_div, Complex.norm_two]
    calc ‖F (z + B * I) + starRingEnd ℂ (F (starRingEnd ℂ z + B * I))‖ / 2
        ≤ (‖F (z + B * I)‖ + ‖F (starRingEnd ℂ z + B * I)‖) / 2 := by
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [Complex.norm_conj]
      _ ≤ (M + M) / 2 := by gcongr
      _ = M := by ring
  have hgc : g σ1 ≠ 0 := fun h => by rw [h, norm_zero] at hgσ; linarith
  obtain ⟨Zs, hZcard, hZs⟩ := exists_finset_real_zeros_card_le_of_jensen g σ1 r R M hr0 hrR hM1 hga
      hgc hbound
  -- Backlund
  set φ : ℝ → ℂ := fun x => F (x + B * I) with hφ
  set φ' : ℝ → ℂ := fun x => deriv F (x + B * I) with hφ'
  have hdA : ∀ x : ℝ, AnalyticAt ℂ F (x + B * I) := by
    intro x
    have hne1 : (x : ℂ) + B * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    exact hFd.analyticAt (isOpen_compl_singleton.mem_nhds hne1)
  have hd : ∀ x ∈ Set.Icc (1 / 2 : ℝ) σ1, HasDerivAt φ (φ' x) x := fun x _ =>
    ((hdA x).differentiableAt.hasDerivAt.comp_add_const (x : ℂ) ((B : ℂ) * I)).comp_ofReal
  have hc : ContinuousOn φ' (Set.Icc (1 / 2 : ℝ) σ1) := fun x _ =>
    ((hdA x).deriv.continuousAt.comp (f := fun x : ℝ => (x : ℂ) + B * I)
      (by fun_prop)).continuousWithinAt
  have hφne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) σ1, φ x ≠ 0 := fun x hx => hne x hx.1 hx.2
  have hbl := abs_im_integral_logDeriv_le_of_re_zeros φ φ' (1 / 2) σ1 hd hc hφne Zs _ (1 / 2) σ1
      le_rfl (by linarith) le_rfl
    rfl (fun x hx hx0 => by
      apply hZs x
      · rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      · rw [hgreal]; simp only [hφ] at hx0; rw [hx0]; simp)
  have hint : (∫ x in (1 / 2 : ℝ)..σ1, logDeriv F ((x : ℂ) + (B : ℂ) * I)) =
      ∫ x in (1 / 2 : ℝ)..σ1, φ' x / φ x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hφ, hφ', logDeriv_apply]
  rw [hint]
  refine hbl.trans ?_
  have hcard : ((Zs.filter (fun x => x ∈ Set.Ioo (1 / 2 : ℝ) σ1)).card : ℝ) ≤ Zs.card := by
    exact_mod_cast Finset.card_filter_le _ _
  have hlogM : Real.log (M / ‖g σ1‖) ≤ c₁ * Real.log B := by
    have h1 : M / ‖g σ1‖ ≤ 2 * M := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : Real.log (M / ‖g σ1‖) ≤ Real.log (2 * M) :=
      Real.log_le_log (div_pos (by linarith) (by linarith)) h1
    have h3 : Real.log (2 * M) = Real.log 2 + Real.log (1 + |C|) + A * (Real.log 2 + Real.log B) :=
        by
      rw [hM, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by
          positivity),
        Real.log_rpow (by linarith), Real.log_mul (by norm_num) (by linarith)]
      ring
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlC : 0 ≤ Real.log (1 + |C|) := Real.log_nonneg (by have := abs_nonneg C; linarith)
    rw [hc₁]
    have : Real.log 2 + Real.log (1 + |C|) + A * (Real.log 2 + Real.log B) ≤
        (Real.log 2 + Real.log (1 + |C|) + A * Real.log 2 + A) * Real.log B := by
      have e : (Real.log 2 + Real.log (1 + |C|) + A * Real.log 2 + A) * Real.log B =
          (Real.log 2 + Real.log (1 + |C|) + A * Real.log 2) * Real.log B + A * Real.log B := by
              ring
      rw [e]
      have : Real.log 2 + Real.log (1 + |C|) + A * Real.log 2 ≤
          (Real.log 2 + Real.log (1 + |C|) + A * Real.log 2) * Real.log B :=
        le_mul_of_one_le_right (by positivity) hlogB
      nlinarith
    linarith
  have hZ' : (Zs.card : ℝ) ≤ c₁ / Real.log (R / r) * Real.log B := by
    refine hZcard.trans ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hlogM hlogRr.le
  have hpi := Real.pi_pos
  have : ((Zs.filter (fun x => x ∈ Set.Ioo (1 / 2 : ℝ) σ1)).card + 1 : ℝ) ≤
      (c₁ / Real.log (R / r) + 1) * Real.log B := by
    have e : (c₁ / Real.log (R / r) + 1) * Real.log B =
        c₁ / Real.log (R / r) * Real.log B + Real.log B := by ring
    rw [e]; linarith
  calc ((Zs.filter (fun x => x ∈ Set.Ioo (1 / 2 : ℝ) σ1)).card + 1 : ℝ) * Real.pi
      ≤ (c₁ / Real.log (R / r) + 1) * Real.log B * Real.pi := by gcongr
    _ = _ := by ring

/-- Heights free of zeros are dense. -/
private lemma exists_zero_free_height (H : ℂ → ℂ) (hH : Differentiable ℂ H) (z0 : ℂ) (hz0 : H z0 ≠
    0)
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) (T : ℝ) :
    ∃ T' ∈ Set.Ioo T (T + 1), ∀ s : ℂ, s.im = T' → H s ≠ 0 := by
  have hfin := (Complex.finite_setOf_eq_zero_norm_le hH hz0 (|T| + 3)).image Complex.im
  obtain ⟨T', hT', hnot⟩ := (Set.Ioo_infinite (show T < T + 1 by linarith)).exists_notMem_finite
    hfin
  refine ⟨T', hT', fun s hs h0 => hnot ⟨s, ⟨h0, ?_⟩, hs⟩⟩
  have h1 := hstrip s h0
  have := Complex.norm_le_abs_re_add_abs_im s
  rw [hs, abs_of_nonneg h1.1] at this
  have : |T'| ≤ |T| + 1 := by
    rw [abs_le]; constructor <;> cases abs_le.1 (le_refl |T|) <;>
      linarith [hT'.1, hT'.2, neg_abs_le T, le_abs_self T]
  linarith [h1.2]

/-- A bottom height `A ∈ (-1, 0)` with no zeros in `A ≤ Im s < 0`. -/
private lemma exists_zero_free_bottom_height (H : ℂ → ℂ) (hH : Differentiable ℂ H) (z0 : ℂ) (hz0 : H
    z0 ≠ 0)
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) :
    ∃ A : ℝ, -1 < A ∧ A < 0 ∧ ∀ s : ℂ, H s = 0 → ¬ (A ≤ s.im ∧ s.im < 0) := by
  have hfin := Complex.finite_setOf_eq_zero_norm_le hH hz0 3
  set Y : Finset ℝ := insert (-1) ((hfin.toFinset.image Complex.im).filter (· < 0)) with hY
  have hYne : Y.Nonempty := ⟨-1, Finset.mem_insert_self _ _⟩
  set y := Y.max' hYne with hy
  have hyneg : y < 0 := by
    rw [hy, Finset.max'_lt_iff]
    intro z hz
    rw [hY, Finset.mem_insert, Finset.mem_filter] at hz
    rcases hz with rfl | ⟨-, hz⟩
    · norm_num
    · exact hz
  have hy1 : -1 ≤ y := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨y / 2, by linarith, by linarith, fun s h0 ⟨hA, hs⟩ => ?_⟩
  have h1 := hstrip s h0
  have hnorm : ‖s‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg h1.1, abs_of_neg hs] at this
    linarith
  have hmem : s.im ∈ Y := by
    rw [hY, Finset.mem_insert, Finset.mem_filter, Finset.mem_image]
    right
    exact ⟨⟨s, by rw [Set.Finite.mem_toFinset]; exact ⟨h0, hnorm⟩, rfl⟩, hs⟩
  have := Finset.le_max' _ _ hmem
  rw [← hy] at this
  linarith

/-- Two zero counts with the same zeros and multiplicities off a finite set `X` differ by at most
the total multiplicity on `X`. -/
private lemma abs_sub_zeroCount_le_of_eq_off_finset (f h : ℂ → ℂ) (X : Finset ℂ) (S : Set ℂ)
    (hSf : {ρ | f ρ = 0 ∧ ρ ∈ S}.Finite) (hSh : {ρ | h ρ = 0 ∧ ρ ∈ S}.Finite)
    (heq : ∀ ρ ∈ S, ρ ∉ X → ((f ρ = 0 ↔ h ρ = 0) ∧ analyticOrderNatAt f ρ = analyticOrderNatAt h ρ))
        :
    |((∑ᶠ ρ ∈ {ρ | f ρ = 0 ∧ ρ ∈ S}, analyticOrderNatAt f ρ : ℕ) : ℝ) -
        ((∑ᶠ ρ ∈ {ρ | h ρ = 0 ∧ ρ ∈ S}, analyticOrderNatAt h ρ : ℕ) : ℝ)| ≤
      ∑ x ∈ X, ((analyticOrderNatAt f x : ℝ) + analyticOrderNatAt h x) := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf, finsum_mem_eq_finite_toFinset_sum _ hSh]
  set Af := hSf.toFinset
  set Ah := hSh.toFinset
  rw [← Finset.sum_filter_add_sum_filter_not Af (· ∈ X),
    ← Finset.sum_filter_add_sum_filter_not Ah (· ∈ X)]
  have hfil : Af.filter (· ∉ X) = Ah.filter (· ∉ X) := by
    ext ρ
    simp only [Finset.mem_filter, Af, Ah, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, hS⟩, hX⟩; exact ⟨⟨(heq ρ hS hX).1.1 h0, hS⟩, hX⟩
    · rintro ⟨⟨h0, hS⟩, hX⟩; exact ⟨⟨(heq ρ hS hX).1.2 h0, hS⟩, hX⟩
  have hsum : ∑ ρ ∈ Af.filter (· ∉ X), analyticOrderNatAt f ρ =
      ∑ ρ ∈ Ah.filter (· ∉ X), analyticOrderNatAt h ρ := by
    rw [hfil]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    simp only [Finset.mem_filter, Ah, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
    exact (heq ρ hρ.1.2 hρ.2).2
  rw [hsum]
  have h1 : ∑ ρ ∈ Af.filter (· ∈ X), analyticOrderNatAt f ρ ≤ ∑ x ∈ X, analyticOrderNatAt f x :=
    Finset.sum_le_sum_of_subset (fun ρ hρ => (Finset.mem_filter.1 hρ).2)
  have h2 : ∑ ρ ∈ Ah.filter (· ∈ X), analyticOrderNatAt h ρ ≤ ∑ x ∈ X, analyticOrderNatAt h x :=
    Finset.sum_le_sum_of_subset (fun ρ hρ => (Finset.mem_filter.1 hρ).2)
  push_cast
  rw [Finset.sum_add_distrib]
  have h1' : (∑ ρ ∈ Af.filter (· ∈ X), (analyticOrderNatAt f ρ : ℝ)) ≤
      ∑ x ∈ X, (analyticOrderNatAt f x : ℝ) := by exact_mod_cast h1
  have h2' : (∑ ρ ∈ Ah.filter (· ∈ X), (analyticOrderNatAt h ρ : ℝ)) ≤
      ∑ x ∈ X, (analyticOrderNatAt h x : ℝ) := by exact_mod_cast h2
  have p1 : 0 ≤ ∑ ρ ∈ Af.filter (· ∈ X), (analyticOrderNatAt f ρ : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have p2 : 0 ≤ ∑ ρ ∈ Ah.filter (· ∈ X), (analyticOrderNatAt h ρ : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

open Complex in
private lemma intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, starRingEnd ℂ (f x) = starRingEnd ℂ (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

open Complex in
/-- **Folding the rectangle `[1 - σ, σ] × [A, B]`** by `s ↦ 1 - s̄`: for an entire `H` with
`H(1 - s̄) = w H̄(s)` and zeros in `0 ≤ Re s ≤ 1`, `π · #zeros = Im J` with `J` the half contour
`1/2 + iA → σ + iA → σ + iB → 1/2 + iB` of `H'/H`. -/
private lemma pi_mul_sum_order_eq_im_halfContour (H : ℂ → ℂ) (w : ℂ) (hH : Differentiable ℂ H) (hw :
    w ≠ 0)
    (hrefl : ∀ s, H (1 - starRingEnd ℂ s) = w * starRingEnd ℂ (H s))
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1)
    (σ A B : ℝ) (hσ : 1 < σ) (hAB : A < B)
    (hA : ∀ s : ℂ, s.im = A → H s ≠ 0) (hB : ∀ s : ℂ, s.im = B → H s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s, s ∈ Z ↔ H s = 0 ∧ A < s.im ∧ s.im < B) :
    Real.pi * ∑ p ∈ Z, ((analyticOrderAt H p).toNat : ℝ) =
      ((∫ x in (1 / 2 : ℝ)..σ, logDeriv H ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, logDeriv H ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, logDeriv H ((σ : ℂ) + (y : ℂ) * I)).im := by
  have hHσ : H σ ≠ 0 := fun h => by
    have := (hstrip _ h).2; simp at this; linarith
  have hfin : ∀ p, analyticOrderAt H p ≠ ⊤ := Complex.analyticOrderAt_ne_top_of_differentiable hH
      hHσ
  have hrefLD := logDeriv_one_sub_conj_eq_neg_conj H w hH hw hrefl
  set z₀ : ℂ := ⟨1 - σ, A⟩ with hz₀
  set w₀ : ℂ := ⟨σ, B⟩ with hw₀
  have hAP := RectilinearRectangle.boundaryIntegral_logDeriv_eq ⟨z₀, w₀⟩ hH Z
    (by
      intro p hp
      obtain ⟨h0, h1, h2⟩ := (hZ p).mp hp
      obtain ⟨r1, r2⟩ := hstrip p h0
      exact ⟨by change 1 - σ < p.re; linarith, by change p.re < σ; linarith, h1, h2⟩)
    (by
      intro s hs h0
      change s ∈ Set.uIcc z₀.re w₀.re ×ℂ Set.uIcc z₀.im w₀.im at hs
      obtain ⟨-, hs2⟩ := Complex.mem_reProdIm.mp hs
      have hs2' : s.im ∈ Set.Icc A B := by
        rw [Set.uIcc_of_le hAB.le] at hs2; exact hs2
      refine (hZ s).mpr ⟨h0, lt_of_le_of_ne hs2'.1 fun h => hA s h.symm h0,
        lt_of_le_of_ne hs2'.2 fun h => hB s h h0⟩) hfin
  simp only [RectilinearRectangle.boundaryIntegral, hz₀, hw₀] at hAP
  set f := logDeriv H with hf
  have hcont : ∀ s : ℂ, H s ≠ 0 → ContinuousAt f s := fun s hs =>
    (hH.analyticAt s).continuousAt_logDeriv hs
  have hhor : ∀ y : ℝ, (y = A ∨ y = B) → ∀ a b : ℝ,
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) MeasureTheory.volume a b := by
    intro y hy a b
    refine ContinuousOn.intervalIntegrable fun x _ => ?_
    refine (hcont _ ?_).comp_continuousWithinAt (by fun_prop)
    rcases hy with rfl | rfl
    · exact hA _ (by simp)
    · exact hB _ (by simp)
  have hsplit : ∀ y : ℝ, (y = A ∨ y = B) →
      ∫ x in (1 - σ)..σ, f ((x : ℂ) + (y : ℂ) * I) =
        (∫ x in (1 - σ)..(1 / 2), f ((x : ℂ) + (y : ℂ) * I)) +
          ∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (y : ℂ) * I) := fun y hy =>
    (intervalIntegral.integral_add_adjacent_intervals (hhor y hy _ _) (hhor y hy _ _)).symm
  have hleftH : ∀ y : ℝ, ∫ x in (1 - σ)..(1 / 2), f ((x : ℂ) + (y : ℂ) * I) =
      -starRingEnd ℂ (∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (y : ℂ) * I)) := by
    intro y
    have e1 : (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) =
        fun x : ℝ => (fun u : ℝ => -starRingEnd ℂ (f ((u : ℂ) + (y : ℂ) * I))) (1 - x) := by
      funext x
      change f _ = -starRingEnd ℂ (f _)
      rw [← hrefLD]
      congr 1
      apply Complex.ext <;> simp
    conv_lhs => rw [e1]
    rw [intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => -starRingEnd ℂ (f ((u : ℂ) + (y : ℂ) * I))) 1,
      intervalIntegral.integral_neg, intervalIntegral_conj]
    norm_num
  have hleftV : ∫ y in A..B, f (((1 - σ : ℝ) : ℂ) + (y : ℂ) * I) =
      -starRingEnd ℂ (∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I)) := by
    rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => ?_
    change f _ = -starRingEnd ℂ (f _)
    rw [← hrefLD]
    congr 1
    apply Complex.ext <;> simp
  rw [hsplit A (Or.inl rfl), hsplit B (Or.inr rfl), hleftH, hleftH, hleftV] at hAP
  have him := congrArg Complex.im hAP
  set a := ∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (A : ℂ) * I)
  set b := ∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (B : ℂ) * I)
  set v := ∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I)
  have hsum : (∑ p ∈ Z, (((analyticOrderAt H p).toNat : ℕ) : ℂ)) =
      ((∑ p ∈ Z, ((analyticOrderAt H p).toNat : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hsum] at him
  simp only [smul_eq_mul, Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.conj_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.conj_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re] at him
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num at him ⊢
  linarith

open Complex in
/-- At a height `B` free of zeros, `π N_H(B)` is the imaginary part of the half contour. -/
private lemma pi_mul_zeroCount_eq_im_halfContour (H : ℂ → ℂ) (w : ℂ) (hH : Differentiable ℂ H) (hw :
    w ≠ 0)
    (hrefl : ∀ s, H (1 - starRingEnd ℂ s) = w * starRingEnd ℂ (H s))
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) (hH2 : H 2 ≠ 0) (σ A B : ℝ) (hσ : 1 < σ)
    (hA0 : A < 0) (hAz : ∀ s : ℂ, H s = 0 → ¬ (A ≤ s.im ∧ s.im < 0)) (hB : 0 < B)
    (hBz : ∀ s : ℂ, s.im = B → H s ≠ 0) :
    Real.pi * ((∑ᶠ ρ ∈ {ρ : ℂ | H ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ B},
        analyticOrderNatAt H ρ : ℕ) : ℝ) =
      ((∫ x in (1 / 2 : ℝ)..σ, logDeriv H ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, logDeriv H ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, logDeriv H ((σ : ℂ) + (y : ℂ) * I)).im := by
  classical
  have hfin : {ρ : ℂ | H ρ = 0 ∧ A < ρ.im ∧ ρ.im < B}.Finite := by
    refine (Complex.finite_setOf_eq_zero_norm_le hH hH2 (1 + |A| + |B|)).subset fun ρ hρ => ⟨hρ.1,
        ?_⟩
    have h1 := hstrip ρ hρ.1
    have := Complex.norm_le_abs_re_add_abs_im ρ
    have : |ρ.im| ≤ |A| + |B| := by
      rw [abs_le]; constructor <;> linarith [hρ.2.1, hρ.2.2, neg_abs_le A, le_abs_self B,
        abs_nonneg A, abs_nonneg B]
    rw [abs_of_nonneg h1.1] at *
    linarith [h1.2]
  set Z := hfin.toFinset with hZ
  have hZmem : ∀ s, s ∈ Z ↔ H s = 0 ∧ A < s.im ∧ s.im < B := by
    intro s; rw [hZ, Set.Finite.mem_toFinset]; rfl
  have hAz' : ∀ s : ℂ, s.im = A → H s ≠ 0 := fun s hs h0 => hAz s h0 ⟨hs.ge, hs ▸ hA0⟩
  have hfold := pi_mul_sum_order_eq_im_halfContour H w hH hw hrefl hstrip σ A B hσ (by linarith)
      hAz' hBz Z hZmem
  rw [← hfold]
  congr 1
  have hset : {ρ : ℂ | H ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ B} = (Z : Set ℂ) := by
    ext ρ
    rw [Finset.mem_coe, hZmem]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, -, h2, h3⟩
      exact ⟨h0, by linarith, lt_of_le_of_ne h3 fun h => hBz ρ h h0⟩
    · rintro ⟨h0, h2, h3⟩
      refine ⟨h0, (hstrip ρ h0).1, ?_, h3.le⟩
      by_contra hneg
      push Not at hneg
      exact hAz ρ h0 ⟨h2.le, hneg⟩
  rw [hset, finsum_mem_coe_finset]
  push_cast
  rfl

open Complex in
/-- The legs of the half contour are integrable for a function continuous on it. -/
private lemma intervalIntegrable_halfContour (f : ℂ → ℂ) (σ A B : ℝ) (hσ : 1 / 2 ≤ σ) (hAB : A ≤ B)
    (hf : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt f s) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (A : ℂ) * I)) MeasureTheory.volume (1 / 2) σ ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (B : ℂ) * I)) MeasureTheory.volume (1 / 2) σ ∧
    IntervalIntegrable (fun y : ℝ => f ((σ : ℂ) + (y : ℂ) * I)) MeasureTheory.volume A B := by
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le hσ] at hx
    exact (hf _ (Or.inl ⟨by simpa using hx.1, by simpa using hx.2, Or.inl (by simp)⟩)
      ).comp_continuousWithinAt (by fun_prop)
  · refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le hσ] at hx
    exact (hf _ (Or.inl ⟨by simpa using hx.1, by simpa using hx.2, Or.inr (by simp)⟩)
      ).comp_continuousWithinAt (by fun_prop)
  · refine ContinuousOn.intervalIntegrable fun y hy => ?_
    rw [Set.uIcc_of_le hAB] at hy
    exact (hf _ (Or.inr ⟨by simp, by simpa using hy.1, by simpa using hy.2⟩)
      ).comp_continuousWithinAt (by fun_prop)

open Complex in
/-- The half contour is additive in the integrand. -/
private lemma halfContour_add (f g h : ℂ → ℂ) (σ A B : ℝ) (hσ : 1 / 2 ≤ σ) (hAB : A ≤ B)
    (hf : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt f s)
    (hg : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt g s)
    (hh : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → h s = f s + g s) :
    (∫ x in (1 / 2 : ℝ)..σ, h ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, h ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, h ((σ : ℂ) + (y : ℂ) * I) =
      ((∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I)) +
      ((∫ x in (1 / 2 : ℝ)..σ, g ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, g ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, g ((σ : ℂ) + (y : ℂ) * I)) := by
  obtain ⟨f1, f2, f3⟩ := intervalIntegrable_halfContour f σ A B hσ hAB hf
  obtain ⟨g1, g2, g3⟩ := intervalIntegrable_halfContour g σ A B hσ hAB hg
  have e1 : (∫ x in (1 / 2 : ℝ)..σ, h ((x : ℂ) + (A : ℂ) * I)) =
      ∫ x in (1 / 2 : ℝ)..σ, (f ((x : ℂ) + (A : ℂ) * I) + g ((x : ℂ) + (A : ℂ) * I)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hσ] at hx
    exact hh _ (Or.inl ⟨by simpa using hx.1, by simpa using hx.2, Or.inl (by simp)⟩)
  have e2 : (∫ x in (1 / 2 : ℝ)..σ, h ((x : ℂ) + (B : ℂ) * I)) =
      ∫ x in (1 / 2 : ℝ)..σ, (f ((x : ℂ) + (B : ℂ) * I) + g ((x : ℂ) + (B : ℂ) * I)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hσ] at hx
    exact hh _ (Or.inl ⟨by simpa using hx.1, by simpa using hx.2, Or.inr (by simp)⟩)
  have e3 : (∫ y in A..B, h ((σ : ℂ) + (y : ℂ) * I)) =
      ∫ y in A..B, (f ((σ : ℂ) + (y : ℂ) * I) + g ((σ : ℂ) + (y : ℂ) * I)) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hAB] at hy
    exact hh _ (Or.inr ⟨by simp, by simpa using hy.1, by simpa using hy.2⟩)
  rw [e1, e2, e3, intervalIntegral.integral_add f1 g1, intervalIntegral.integral_add f2 g2,
    intervalIntegral.integral_add f3 g3]
  ring

open Complex in
/-- The half contour of a finite sum. -/
private lemma halfContour_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (σ A B : ℝ) (hσ : 1 / 2 ≤
    σ)
    (hAB : A ≤ B)
    (hf : ∀ i ∈ S, ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt (f i) s) :
    (∫ x in (1 / 2 : ℝ)..σ, ∑ i ∈ S, f i ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, ∑ i ∈ S, f i ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, ∑ i ∈ S, f i ((σ : ℂ) + (y : ℂ) * I) =
      ∑ i ∈ S, ((∫ x in (1 / 2 : ℝ)..σ, f i ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, f i ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, f i ((σ : ℂ) + (y : ℂ) * I)) := by
  rw [intervalIntegral.integral_finsetSum (fun i hi => (intervalIntegrable_halfContour _ σ A B hσ
      hAB (hf i hi)).1),
    intervalIntegral.integral_finsetSum (fun i hi => (intervalIntegrable_halfContour _ σ A B hσ hAB
        (hf i hi)).2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (intervalIntegrable_halfContour _ σ A B hσ hAB
        (hf i hi)).2.2),
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

open Complex in
/-- The half contour of a derivative `f = Φ'` (along the path only) is
`Φ(1/2 + iB) - Φ(1/2 + iA)`. -/
private lemma halfContour_eq_sub_of_hasDerivAt (Φ f : ℂ → ℂ) (σ A B : ℝ) (hσ : 1 / 2 ≤ σ) (hAB : A ≤
    B)
    (hd : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → HasDerivAt Φ (f s) s)
    (hf : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt f s) :
    (∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I) =
      Φ (1 / 2 + (B : ℂ) * I) - Φ (1 / 2 + (A : ℂ) * I) := by
  obtain ⟨f1, f2, f3⟩ := intervalIntegrable_halfContour f σ A B hσ hAB hf
  have hor : ∀ y : ℝ, (y = A ∨ y = B) →
      ∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (y : ℂ) * I) =
        Φ ((σ : ℂ) + (y : ℂ) * I) - Φ (1 / 2 + (y : ℂ) * I) := by
    intro y hy
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Φ ((x : ℂ) + (y : ℂ) * I)) (a := 1 / 2) (b := σ)
      (f' := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (fun x hx => by
        rw [Set.uIcc_of_le hσ] at hx
        have hp : (1 / 2 ≤ ((x : ℂ) + (y : ℂ) * I).re ∧ ((x : ℂ) + (y : ℂ) * I).re ≤ σ ∧
            (((x : ℂ) + (y : ℂ) * I).im = A ∨ ((x : ℂ) + (y : ℂ) * I).im = B)) ∨
            (((x : ℂ) + (y : ℂ) * I).re = σ ∧ A ≤ ((x : ℂ) + (y : ℂ) * I).im ∧
              ((x : ℂ) + (y : ℂ) * I).im ≤ B) := Or.inl ⟨by simpa using hx.1,
                by simpa using hx.2, by simpa using hy⟩
        exact ((hd _ hp).comp_add_const (x : ℂ) ((y : ℂ) * I)).comp_ofReal) (by
        rcases hy with rfl | rfl
        · exact f1
        · exact f2)
    rw [h]
    push_cast
    ring_nf
  have hv : ∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I) * I =
      Φ ((σ : ℂ) + (B : ℂ) * I) - Φ ((σ : ℂ) + (A : ℂ) * I) := by
    have hp : ∀ y : ℝ, HasDerivAt (fun y : ℝ => (σ : ℂ) + (y : ℂ) * I) I y := by
      intro y
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * I))]
    · intro y hy
      rw [Set.uIcc_of_le hAB] at hy
      exact (hd _ (Or.inr ⟨by simp, by simpa using hy.1, by simpa using hy.2⟩)).comp y (hp y)
    · exact f3.mul_const I
  rw [hor A (Or.inl rfl), hor B (Or.inr rfl), intervalIntegral.integral_mul_const] at *
  rw [mul_comm I, hv]
  ring

open Complex in
/-- A bound for the half contour from a bound on the path. -/
private lemma norm_halfContour_le (f : ℂ → ℂ) (σ A B M : ℝ) (hσ : 1 / 2 ≤ σ) (hAB : A ≤ B)
    (hM : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → ‖f s‖ ≤ M) :
    ‖(∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M * (2 * (σ - 1 / 2) + (B - A)) := by
  have hh : ∀ y : ℝ, (y = A ∨ y = B) →
      ‖∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (y : ℂ) * I)‖ ≤ M * |σ - 1 / 2| := by
    intro y hy
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hσ] at hx
    exact hM _ (Or.inl ⟨by simpa using hx.1.le, by simpa using hx.2, by simpa using hy⟩)
  have hv : ‖∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M * |B - A| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [Set.uIoc_of_le hAB] at hy
    exact hM _ (Or.inr ⟨by simp, by simpa using hy.1.le, by simpa using hy.2⟩)
  have h1 := hh A (Or.inl rfl)
  have h2 := hh B (Or.inr rfl)
  rw [abs_of_nonneg (by linarith)] at h1 h2
  rw [abs_of_nonneg (by linarith)] at hv
  calc _ ≤ ‖(∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (A : ℂ) * I))‖ +
        ‖(∫ x in (1 / 2 : ℝ)..σ, f ((x : ℂ) + (B : ℂ) * I))‖ +
        ‖I * ∫ y in A..B, f ((σ : ℂ) + (y : ℂ) * I)‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
    _ ≤ M * (σ - 1 / 2) + M * (σ - 1 / 2) + M * (B - A) := by
          rw [norm_mul, Complex.norm_I, one_mul]
          gcongr
    _ = _ := by ring

/-- `Im (w log w - w) = α B log B + O(B)` at `w = α (1/2 + iB) + r`. -/
private lemma abs_im_mul_log_sub_sub_le (α : ℝ) (hα : 0 < α) (r : ℂ) (hr : 0 ≤ r.re) :
    ∃ C B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
      |(((α : ℂ) * (1 / 2 + (B : ℂ) * Complex.I) + r) *
          Complex.log ((α : ℂ) * (1 / 2 + (B : ℂ) * Complex.I) + r) -
          ((α : ℂ) * (1 / 2 + (B : ℂ) * Complex.I) + r)).im - α * B * Real.log B| ≤ C * B := by
  set u : ℝ := α / 2 + r.re with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  set K : ℝ := u + α + |r.im| with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  set L : ℝ := |Real.log (α / 2)| + |Real.log K| with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨α * L + |r.im| * (1 + L) + 2 * u + α + |r.im|, max 1 ((2 * |r.im| + 1) / α),
    fun B hB => ?_⟩
  have hB1 : 1 ≤ B := le_trans (le_max_left _ _) hB
  have hB2 : (2 * |r.im| + 1) / α ≤ B := le_trans (le_max_right _ _) hB
  rw [div_le_iff₀ hα] at hB2
  set w : ℂ := (α : ℂ) * (1 / 2 + (B : ℂ) * Complex.I) + r with hw
  set v : ℝ := α * B + r.im with hv
  have hwre : w.re = u := by rw [hw, hu]; simp; ring
  have hwim : w.im = v := by rw [hw, hv]; simp
  have hv1 : α * B / 2 ≤ v := by
    have := neg_abs_le r.im; rw [hv]; nlinarith
  have hv0 : 0 < v := by nlinarith
  have hn1 : α * B / 2 ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos hv0] at this; linarith
  have hn2 : ‖w‖ ≤ K * B := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_of_pos hu0, abs_of_pos hv0] at this
    rw [hK]
    have : r.im ≤ |r.im| := le_abs_self _
    have h1 : u ≤ u * B := le_mul_of_one_le_right hu0.le hB1
    have h2 : |r.im| ≤ |r.im| * B := le_mul_of_one_le_right (abs_nonneg _) hB1
    have e : (u + α + |r.im|) * B = u * B + α * B + |r.im| * B := by ring
    rw [e]; linarith
  have hwpos : 0 < ‖w‖ := by nlinarith
  have hlogL : |Real.log ‖w‖ - Real.log B| ≤ L := by
    have h1 : Real.log (α * B / 2) ≤ Real.log ‖w‖ := Real.log_le_log (by positivity) hn1
    have h2 : Real.log ‖w‖ ≤ Real.log (K * B) := Real.log_le_log hwpos hn2
    rw [show α * B / 2 = (α / 2) * B by ring, Real.log_mul (by positivity) (by positivity)] at h1
    rw [Real.log_mul hK0.ne' (by positivity)] at h2
    have := le_abs_self (Real.log K)
    have := neg_abs_le (Real.log (α / 2))
    rw [abs_le, hL]
    constructor <;> linarith [abs_nonneg (Real.log K), abs_nonneg (Real.log (α / 2))]
  have hlogB : Real.log B ≤ B := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < B); linarith
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have him : (w * Complex.log w - w).im = v * Real.log ‖w‖ + u * Complex.arg w - v := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.log_re, Complex.log_im, hwre, hwim]
    ring
  rw [him]
  have harg : |Complex.arg w| ≤ 2 := by
    have := Complex.abs_arg_le_pi_div_two_iff.2 (by rw [hwre]; exact hu0.le)
    have := Real.pi_le_four; linarith
  have e : v * Real.log ‖w‖ + u * Complex.arg w - v - α * B * Real.log B =
      α * B * (Real.log ‖w‖ - Real.log B) + r.im * Real.log ‖w‖ + u * Complex.arg w - v := by
    rw [hv]; ring
  rw [e]
  have t1 : |α * B * (Real.log ‖w‖ - Real.log B)| ≤ α * L * B := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc α * B * |Real.log ‖w‖ - Real.log B| ≤ α * B * L :=
          mul_le_mul_of_nonneg_left hlogL (by positivity)
      _ = α * L * B := by ring
  have t2 : |r.im * Real.log ‖w‖| ≤ |r.im| * (1 + L) * B := by
    rw [abs_mul]
    have : |Real.log ‖w‖| ≤ B + L := by
      have := abs_sub_abs_le_abs_sub (Real.log ‖w‖) (Real.log B)
      rw [abs_of_nonneg hlogB0] at this
      linarith
    calc |r.im| * |Real.log ‖w‖| ≤ |r.im| * (B + L) := by gcongr
      _ ≤ |r.im| * (1 + L) * B := by
        have : B + L ≤ (1 + L) * B := by nlinarith
        calc |r.im| * (B + L) ≤ |r.im| * ((1 + L) * B) := by gcongr
          _ = _ := by ring
  have t3 : |u * Complex.arg w| ≤ 2 * u * B := by
    rw [abs_mul, abs_of_pos hu0]; nlinarith
  have t4 : |v| ≤ (α + |r.im|) * B := by
    rw [abs_of_pos hv0, hv]
    have := le_abs_self r.im
    have h2 : |r.im| ≤ |r.im| * B := le_mul_of_one_le_right (abs_nonneg _) hB1
    have e : (α + |r.im|) * B = α * B + |r.im| * B := by ring
    rw [e]; linarith
  calc |α * B * (Real.log ‖w‖ - Real.log B) + r.im * Real.log ‖w‖ + u * Complex.arg w - v|
      ≤ |α * B * (Real.log ‖w‖ - Real.log B)| + |r.im * Real.log ‖w‖| + |u * Complex.arg w|
        + |v| := by
        have := abs_add_le (α * B * (Real.log ‖w‖ - Real.log B) + r.im * Real.log ‖w‖ +
          u * Complex.arg w) (-v)
        have := abs_add_le (α * B * (Real.log ‖w‖ - Real.log B) + r.im * Real.log ‖w‖)
          (u * Complex.arg w)
        have := abs_add_le (α * B * (Real.log ‖w‖ - Real.log B)) (r.im * Real.log ‖w‖)
        rw [abs_neg] at *
        rw [sub_eq_add_neg]
        linarith
    _ ≤ α * L * B + |r.im| * (1 + L) * B + 2 * u * B + (α + |r.im|) * B := by
        linarith
    _ = _ := by ring

open Complex in
/-- The archimedean part of the half contour: `Im J(α ψ(α s + r)) = α B log B + O(B)`. -/
private lemma abs_im_halfContour_digamma_sub_le (α : ℝ) (hα : 0 < α) (r : ℂ) (hr : 0 ≤ r.re) (σ A :
    ℝ)
    (hσ : 1 / 2 ≤ σ) :
    ∃ C B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → A ≤ B →
      |((∫ x in (1 / 2 : ℝ)..σ, (α : ℂ) * digamma ((α : ℂ) * ((x : ℂ) + (A : ℂ) * I) + r)) -
        (∫ x in (1 / 2 : ℝ)..σ, (α : ℂ) * digamma ((α : ℂ) * ((x : ℂ) + (B : ℂ) * I) + r)) +
        I * ∫ y in A..B, (α : ℂ) * digamma ((α : ℂ) * ((σ : ℂ) + (y : ℂ) * I) + r)).im -
        α * B * Real.log B| ≤ C * B := by
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  obtain ⟨C₁, B₁, hmain⟩ := abs_im_mul_log_sub_sub_le α hα r hr
  set W : ℂ → ℂ := fun s => ((α : ℂ) * s + r) * Complex.log ((α : ℂ) * s + r) -
    ((α : ℂ) * s + r) with hW
  set cA : ℝ := (W (1 / 2 + (A : ℂ) * I)).im with hcA
  refine ⟨C₁ + |cA| + 2 * |Cd| * (2 * σ + |A| + 2), max B₁ 1, fun B hB hAB => ?_⟩
  have hB1 : 1 ≤ B := le_trans (le_max_right _ _) hB
  have hBB : B₁ ≤ B := le_trans (le_max_left _ _) hB
  have hre : ∀ s : ℂ, 1 / 2 ≤ s.re → α / 2 ≤ ((α : ℂ) * s + r).re := fun s hs => by
    simp only [Complex.add_re, Complex.re_ofReal_mul]; nlinarith
  have hre' : ∀ s : ℂ, 1 / 2 ≤ s.re → 0 < ((α : ℂ) * s + r).re := fun s hs => by
    have := hre s hs; linarith
  have hslit : ∀ s : ℂ, 1 / 2 ≤ s.re → (α : ℂ) * s + r ∈ slitPlane := fun s hs =>
    Or.inl (hre' s hs)
  have hne : ∀ s : ℂ, 1 / 2 ≤ s.re → (α : ℂ) * s + r ≠ 0 := fun s hs h => by
    have := hre' s hs; rw [h] at this; simp at this
  have hpath : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → 1 / 2 ≤ s.re := by
    rintro s (⟨h, -, -⟩ | ⟨h, -⟩)
    · exact h
    · rw [h]; exact hσ
  have hlin : ∀ s : ℂ, HasDerivAt (fun s : ℂ => (α : ℂ) * s + r) (α : ℂ) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul (α : ℂ)).add_const r
  have hWd : ∀ s : ℂ, 1 / 2 ≤ s.re → HasDerivAt W ((α : ℂ) * Complex.log ((α : ℂ) * s + r)) s := by
    intro s hs
    have hl := (hlin s).clog (hslit s hs)
    have := ((hlin s).mul hl).sub (hlin s)
    refine this.congr_deriv ?_
    have := hne s hs
    field_simp
    ring
  have hlogc : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ContinuousAt (fun s : ℂ => (α : ℂ) * Complex.log ((α : ℂ) * s + r)) s := fun s hs =>
    continuousAt_const.mul ((continuousAt_clog (hslit s hs)).comp
      (f := fun s : ℂ => (α : ℂ) * s + r) (by fun_prop))
  have hψc : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ContinuousAt (fun s : ℂ => (α : ℂ) * digamma ((α : ℂ) * s + r)) s := fun s hs =>
    continuousAt_const.mul ((Complex.continuousAt_digamma_of_re_pos (hre' s hs)).comp
      (f := fun s : ℂ => (α : ℂ) * s + r) (by fun_prop))
  set gerr : ℂ → ℂ := fun s => (α : ℂ) * digamma ((α : ℂ) * s + r) -
    (α : ℂ) * Complex.log ((α : ℂ) * s + r) with hgerr
  have hsplit := halfContour_add (fun s : ℂ => (α : ℂ) * Complex.log ((α : ℂ) * s + r)) gerr
    (fun s : ℂ => (α : ℂ) * digamma ((α : ℂ) * s + r)) σ A B hσ hAB
    (fun s hs => hlogc s (hpath s hs)) (fun s hs => (hψc s (hpath s hs)).sub (hlogc s (hpath s hs)))
    (fun s _ => by simp only [hgerr]; ring)
  have hprim := halfContour_eq_sub_of_hasDerivAt W (fun s : ℂ => (α : ℂ) * Complex.log ((α : ℂ) * s
      + r)) σ A B hσ hAB
    (fun s hs => hWd s (hpath s hs)) (fun s hs => hlogc s (hpath s hs))
  have herr : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖gerr s‖ ≤ 2 * |Cd| := by
    intro s hs
    have hw0 := hne s hs
    have harg' := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr (hre' s hs).le)
    have h := hCd _ hw0 (by linarith [harg'.1]) (by linarith [harg'.2])
    have hn : α / 2 ≤ ‖(α : ℂ) * s + r‖ := (hre s hs).trans (Complex.re_le_norm _)
    simp only [hgerr]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
    have h2 : Cd / ‖(α : ℂ) * s + r‖ ≤ |Cd| / (α / 2) := by
      calc Cd / ‖(α : ℂ) * s + r‖ ≤ |Cd| / ‖(α : ℂ) * s + r‖ :=
            div_le_div_of_nonneg_right (le_abs_self Cd) (by positivity)
        _ ≤ |Cd| / (α / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hn
    have h3 := h.trans h2
    calc α * ‖digamma ((α : ℂ) * s + r) - Complex.log ((α : ℂ) * s + r)‖
        ≤ α * (|Cd| / (α / 2)) := by gcongr
      _ = 2 * |Cd| := by field_simp
  have hJerr := norm_halfContour_le gerr σ A B (2 * |Cd|) hσ hAB (fun s hs => herr s (hpath s hs))
  rw [hsplit, hprim, Complex.add_im, Complex.sub_im]
  have hm := hmain B hBB
  simp only [hW] at hm hcA ⊢
  have hJ := (Complex.abs_im_le_norm _).trans hJerr
  have hcAB : |cA| ≤ |cA| * B := le_mul_of_one_le_right (abs_nonneg _) hB1
  have hE : 2 * |Cd| * (2 * (σ - 1 / 2) + (B - A)) ≤ 2 * |Cd| * (2 * σ + |A| + 2) * B := by
    have h0 : 0 ≤ 2 * |Cd| := by positivity
    have : 2 * (σ - 1 / 2) + (B - A) ≤ (2 * σ + |A| + 2) * B := by
      have := neg_abs_le A
      have : 0 ≤ σ := by linarith
      have h1 : 2 * σ ≤ 2 * σ * B := le_mul_of_one_le_right (by linarith) hB1
      have h2 : |A| ≤ |A| * B := le_mul_of_one_le_right (abs_nonneg _) hB1
      have e : (2 * σ + |A| + 2) * B = 2 * σ * B + |A| * B + 2 * B := by ring
      rw [e]; linarith
    calc 2 * |Cd| * (2 * (σ - 1 / 2) + (B - A)) ≤ 2 * |Cd| * ((2 * σ + |A| + 2) * B) := by
          gcongr
      _ = _ := by ring
  rw [← hcA]
  rw [abs_le] at hm hJ ⊢
  have := le_abs_self cA
  have := neg_abs_le cA
  constructor <;> nlinarith

open Complex in
/-- The rational and constant part of `H'/H`: `Im J(m/s + log Q + m/(s-1)) = B log Q + O(1)`. -/
private lemma abs_im_halfContour_rational_sub_le (m : ℕ) (Q : ℝ) (hQ : 0 < Q) (σ A B : ℝ) (hσ : 2 ≤
    σ) (hA : A < 0)
    (hB : 0 < B) :
    |((∫ x in (1 / 2 : ℝ)..σ, ((m : ℂ) / ((x : ℂ) + (A : ℂ) * I) + Complex.log Q +
          (m : ℂ) / ((x : ℂ) + (A : ℂ) * I - 1))) -
        (∫ x in (1 / 2 : ℝ)..σ, ((m : ℂ) / ((x : ℂ) + (B : ℂ) * I) + Complex.log Q +
          (m : ℂ) / ((x : ℂ) + (B : ℂ) * I - 1))) +
        I * ∫ y in A..B, ((m : ℂ) / ((σ : ℂ) + (y : ℂ) * I) + Complex.log Q +
          (m : ℂ) / ((σ : ℂ) + (y : ℂ) * I - 1))).im - Real.log Q * B| ≤
      4 * Real.pi * m + |Real.log Q * A| := by
  set f : ℂ → ℂ := fun s => (m : ℂ) / s + Complex.log Q + (m : ℂ) / (s - 1) with hf
  set Φ : ℂ → ℂ := fun s => (m : ℂ) * Complex.log s + Complex.log Q * s +
    (m : ℂ) * Complex.log (s - 1) with hΦ
  have hpath : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → s ∈ slitPlane ∧ s - 1 ∈ slitPlane := by
    rintro s (⟨h1, -, h3⟩ | ⟨h1, h2, h3⟩)
    · refine ⟨Or.inl (by linarith), Or.inr ?_⟩
      simp only [Complex.sub_im, Complex.one_im, sub_zero]
      rcases h3 with h | h <;> rw [h] <;> [exact hA.ne; exact hB.ne']
    · refine ⟨Or.inl (by rw [h1]; linarith), Or.inl ?_⟩
      simp only [Complex.sub_re, Complex.one_re]; rw [h1]; linarith
  have hne : ∀ s : ℂ, s ∈ slitPlane → s ≠ 0 := fun s hs => slitPlane_ne_zero hs
  have hd : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → HasDerivAt Φ (f s) s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hpath s hs
    have e1 := ((hasDerivAt_id s).clog h1).const_mul (m : ℂ)
    have e2 := (hasDerivAt_id s).const_mul (Complex.log Q)
    have e3 := (((hasDerivAt_id s).sub_const 1).clog h2).const_mul (m : ℂ)
    have := (e1.add e2).add e3
    refine this.congr_deriv ?_
    simp only [hf, id]
    field_simp
  have hc : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt f s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hpath s hs
    have h1' := hne s h1
    have h2' := hne _ h2
    simp only [hf]
    exact ((continuousAt_const.div continuousAt_id h1').add continuousAt_const).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) h2')
  have hJ := halfContour_eq_sub_of_hasDerivAt Φ f σ A B (by linarith) (by linarith) hd hc
  simp only [hf] at hJ
  rw [hJ]
  simp only [hΦ, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, Complex.log_im, zero_mul, add_zero]
  have hlQ : Complex.log (Q : ℂ) = (Real.log Q : ℂ) := (Complex.ofReal_log hQ.le).symm
  rw [hlQ]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im]
  norm_num
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have bnd : ∀ z : ℂ, -(m * Real.pi) ≤ m * z.arg ∧ m * z.arg ≤ m * Real.pi := by
    intro z
    have := abs_le.1 (Complex.abs_arg_le_pi z)
    exact ⟨by nlinarith [this.1], mul_le_mul_of_nonneg_left this.2 hm⟩
  have b1 := bnd (1 / 2 + B * I)
  have b2 := bnd (1 / 2 + A * I)
  have b3 := bnd (1 / 2 + B * I - 1)
  have b4 := bnd (1 / 2 + A * I - 1)
  have hLA : |Real.log Q * A| = |Real.log Q| * |A| := abs_mul _ _
  have := neg_abs_le (Real.log Q * A)
  have := le_abs_self (Real.log Q * A)
  rw [abs_le]
  constructor <;> nlinarith

open Complex in
/-- **The half contour of `H'/H`**: `Im J = (∑ α_i) B log B + O(B)` at heights `B` free of zeros. -/
private lemma abs_im_halfContour_logDeriv_completed_sub_le (F G H : ℂ → ℂ) (m : ℕ) (hFd :
    DifferentiableOn ℂ F {1}ᶜ)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) (D : FunctionalEquation F)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Complex.Gamma (D.α i * s + D.r i)) * G s)
    (σ1 K Kt B₁ A : ℝ) (hσ1 : 2 ≤ σ1) (hnear : ∀ s : ℂ, σ1 ≤ s.re → ‖F s - 1‖ ≤ 1 / 2)
    (hK : ∀ s : ℂ, σ1 ≤ s.re → ‖logDeriv F s‖ ≤ K)
    (htop : ∀ B : ℝ, B₁ ≤ B → (∀ x : ℝ, 1 / 2 ≤ x → x ≤ σ1 → F (x + B * I) ≠ 0) →
      |(∫ x in (1 / 2 : ℝ)..σ1, logDeriv F ((x : ℂ) + (B : ℂ) * I)).im| ≤ Kt * Real.log B)
    (hA1 : -1 < A) (hA0 : A < 0) (hAz : ∀ s : ℂ, s.im = A → H s ≠ 0) :
    ∃ C B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → (∀ s : ℂ, s.im = B → H s ≠ 0) →
      |((∫ x in (1 / 2 : ℝ)..σ1, logDeriv H ((x : ℂ) + (A : ℂ) * I)) -
        (∫ x in (1 / 2 : ℝ)..σ1, logDeriv H ((x : ℂ) + (B : ℂ) * I)) +
        I * ∫ y in A..B, logDeriv H ((σ1 : ℂ) + (y : ℂ) * I)).im -
        (∑ i, D.α i) * B * Real.log B| ≤ C * B := by
  choose Cg Bg hg using fun i => abs_im_halfContour_digamma_sub_le (D.α i) (D.α_pos i) (D.r i)
      (D.r_re_nonneg i)
    σ1 A (by linarith)
  set ca : ℝ := (∫ x in (1 / 2 : ℝ)..σ1, logDeriv F ((x : ℂ) + (A : ℂ) * I)).im with hca
  set crat : ℝ := 4 * Real.pi * m + |Real.log D.Q * A| with hcrat
  refine ⟨|Real.log D.Q| + crat + ∑ i, |Cg i| + |ca| + |Kt| + 2 * |K|,
    max (max B₁ 1) (∑ i, |Bg i|), fun B hB hBz => ?_⟩
  have hB1 : 1 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hBB₁ : B₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBg : ∀ i, Bg i ≤ B := fun i => by
    have := Finset.single_le_sum (f := fun i => |Bg i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := le_abs_self (Bg i)
    have := le_trans (le_max_right _ _) hB
    linarith
  have hAB : A ≤ B := by linarith
  have hσ : 1 / 2 ≤ σ1 := by linarith
  -- facts on the path
  have hHF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → H s ≠ 0 → F s ≠ 0 := by
    intro s hs hs1 hH hF
    apply hH
    rw [hHr s hs, hGF s hs1, hF]; simp
  have hpath : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ1 ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ1 ∧ A ≤ s.im ∧ s.im ≤ B) → 1 / 2 ≤ s.re ∧ s ≠ 1 ∧ F s ≠ 0 := by
    rintro s (⟨h1, -, h3⟩ | ⟨h1, -, -⟩)
    · have hs1 : s ≠ 1 := by
        rintro rfl
        rcases h3 with h | h <;> simp at h <;> linarith
      refine ⟨h1, hs1, hHF s (by linarith) hs1 ?_⟩
      rcases h3 with h | h
      · exact hAz s h
      · exact hBz s h
    · have hs1 : s ≠ 1 := by rintro rfl; simp at h1; linarith
      refine ⟨by rw [h1]; exact hσ, hs1, fun h0 => ?_⟩
      have := hnear s (by rw [h1])
      rw [h0, zero_sub, norm_neg, norm_one] at this
      linarith
  set rat : ℂ → ℂ := fun s => (m : ℂ) / s + Complex.log D.Q + (m : ℂ) / (s - 1) with hrat
  set gam : ℂ → ℂ := fun s => ∑ i, (D.α i : ℂ) * digamma (D.α i * s + D.r i) with hgam
  have hratc : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ1 ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ1 ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt rat s := by
    intro s hs
    obtain ⟨h1, h2, -⟩ := hpath s hs
    have h0 : s ≠ 0 := by rintro rfl; simp at h1; linarith
    exact ((continuousAt_const.div continuousAt_id h0).add continuousAt_const).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 h2))
  have hre : ∀ i, ∀ s : ℂ, 1 / 2 ≤ s.re → 0 < ((D.α i : ℂ) * s + D.r i).re := by
    intro i s hs
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    have := D.α_pos i; have := D.r_re_nonneg i; nlinarith
  have hgamc' : ∀ i ∈ (Finset.univ : Finset (Fin D.d)), ∀ s : ℂ,
      (1 / 2 ≤ s.re ∧ s.re ≤ σ1 ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ1 ∧ A ≤ s.im ∧ s.im ≤ B) →
        ContinuousAt (fun s : ℂ => (D.α i : ℂ) * digamma (D.α i * s + D.r i)) s := by
    intro i _ s hs
    exact continuousAt_const.mul ((Complex.continuousAt_digamma_of_re_pos (hre i s (hpath s
        hs).1)).comp
      (f := fun s : ℂ => (D.α i : ℂ) * s + D.r i) (by fun_prop))
  have hgamc : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ1 ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ1 ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt gam s := by
    intro s hs
    exact tendsto_finsetSum Finset.univ (fun i hi => hgamc' i hi s hs)
  have hFc : ∀ s : ℂ, (1 / 2 ≤ s.re ∧ s.re ≤ σ1 ∧ (s.im = A ∨ s.im = B)) ∨
      (s.re = σ1 ∧ A ≤ s.im ∧ s.im ≤ B) → ContinuousAt (logDeriv F) s := by
    intro s hs
    obtain ⟨-, h2, h3⟩ := hpath s hs
    exact AnalyticAt.continuousAt_logDeriv
      (hFd.analyticAt (isOpen_compl_singleton.mem_nhds h2)) h3
  have hsplit1 := halfContour_add (fun s => rat s + gam s) (logDeriv F) (logDeriv H) σ1 A B hσ hAB
    (fun s hs => (hratc s hs).add (hgamc s hs)) hFc (fun s hs => by
      obtain ⟨h1, h2, h3⟩ := hpath s hs
      rw [logDeriv_completed F G H m hFd hGF D hHr s (by linarith) h2 h3]
      simp only [hrat, hgam]; ring)
  have hsplit2 := halfContour_add rat gam (fun s => rat s + gam s) σ1 A B hσ hAB hratc hgamc
    (fun s _ => rfl)
  have hsum := halfContour_sum Finset.univ (fun i (s : ℂ) => (D.α i : ℂ) * digamma (D.α i * s + D.r
      i))
    σ1 A B hσ hAB hgamc'
  rw [hsplit1, hsplit2]
  simp only [hgam]
  rw [hsum]
  have hR := abs_im_halfContour_rational_sub_le m D.Q D.Q_pos σ1 A B hσ1 hA0 (by linarith)
  simp only [hrat] at hR ⊢
  -- the F part
  set aF := ∫ x in (1 / 2 : ℝ)..σ1, logDeriv F ((x : ℂ) + (A : ℂ) * I)
  set bF := ∫ x in (1 / 2 : ℝ)..σ1, logDeriv F ((x : ℂ) + (B : ℂ) * I)
  set vF := ∫ y in A..B, logDeriv F ((σ1 : ℂ) + (y : ℂ) * I)
  have hbF : |bF.im| ≤ Kt * Real.log B := htop B hBB₁ (fun x hx1 hx2 => by
    have := (hpath ((x : ℂ) + (B : ℂ) * I) (Or.inl ⟨by simpa using hx1, by simpa using hx2,
      Or.inr (by simp)⟩)).2.2
    exact this)
  have hvF : ‖vF‖ ≤ K * (B - A) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := A) (b := B) (C := K)
      (f := fun y : ℝ => logDeriv F ((σ1 : ℂ) + (y : ℂ) * I)) (fun y _ => hK _ (by simp))
    rwa [abs_of_nonneg (by linarith)] at this
  have hlogB : Real.log B ≤ B := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < B); linarith
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hFim : |(aF - bF + I * vF).im| ≤ |ca| + |Kt| * B + 2 * |K| * B := by
    have e : (aF - bF + I * vF).im = ca - bF.im + vF.re := by
      simp [hca, aF, Complex.sub_im, Complex.add_im, Complex.mul_im]
    rw [e]
    have h1 : |vF.re| ≤ 2 * |K| * B := by
      refine (Complex.abs_re_le_norm _).trans (hvF.trans ?_)
      have : K ≤ |K| := le_abs_self K
      have : 0 ≤ B - A := by linarith
      have : B - A ≤ 2 * B := by linarith
      calc K * (B - A) ≤ |K| * (B - A) := by gcongr
        _ ≤ |K| * (2 * B) := by gcongr
        _ = 2 * |K| * B := by ring
    have h2 : |bF.im| ≤ |Kt| * B := by
      refine hbF.trans ?_
      calc Kt * Real.log B ≤ |Kt| * Real.log B := by gcongr; exact le_abs_self Kt
        _ ≤ |Kt| * B := by gcongr
    calc |ca - bF.im + vF.re| ≤ |ca| + |bF.im| + |vF.re| := by
          have := abs_add_le (ca - bF.im) vF.re
          have := abs_sub (ca) (bF.im)
          linarith
      _ ≤ _ := by linarith
  -- the gamma part
  have hG : ∀ i, |(((∫ x in (1 / 2 : ℝ)..σ1, (D.α i : ℂ) * digamma ((D.α i : ℂ) *
        ((x : ℂ) + (A : ℂ) * I) + D.r i)) -
      (∫ x in (1 / 2 : ℝ)..σ1, (D.α i : ℂ) * digamma ((D.α i : ℂ) *
        ((x : ℂ) + (B : ℂ) * I) + D.r i)) +
      I * ∫ y in A..B, (D.α i : ℂ) * digamma ((D.α i : ℂ) * ((σ1 : ℂ) + (y : ℂ) * I) + D.r i)).im) -
      D.α i * B * Real.log B| ≤ |Cg i| * B := fun i =>
    (hg i B (hBg i) hAB).trans (by gcongr; exact le_abs_self _)
  have hGsum : |(∑ i, ((∫ x in (1 / 2 : ℝ)..σ1, (D.α i : ℂ) * digamma ((D.α i : ℂ) *
        ((x : ℂ) + (A : ℂ) * I) + D.r i)) -
      (∫ x in (1 / 2 : ℝ)..σ1, (D.α i : ℂ) * digamma ((D.α i : ℂ) *
        ((x : ℂ) + (B : ℂ) * I) + D.r i)) +
      I * ∫ y in A..B, (D.α i : ℂ) * digamma ((D.α i : ℂ) * ((σ1 : ℂ) + (y : ℂ) * I) +
        D.r i))).im - (∑ i, D.α i) * B * Real.log B| ≤ (∑ i, |Cg i|) * B := by
    rw [Complex.im_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hG i)
  rw [Complex.add_im, Complex.add_im]
  have hcr : crat ≤ crat * B := le_mul_of_one_le_right (by positivity) hB1
  have hca' : |ca| ≤ |ca| * B := le_mul_of_one_le_right (abs_nonneg _) hB1
  have hlQ : |Real.log D.Q * B| ≤ |Real.log D.Q| * B := by
    rw [abs_mul, abs_of_pos (show (0:ℝ) < B by linarith)]
  rw [abs_le] at hR hGsum hFim hlQ ⊢
  constructor <;> nlinarith

/-- Far to the right, `F` is close to `1` and `F'/F` is bounded. -/
private lemma exists_norm_sub_one_le_and_norm_logDeriv_le (a : ArithmeticFunction ℂ) (F : ℂ → ℂ)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries (fun n => a n) s) (ha1 : a 1 = 1) (Ca : ℝ)
    (hCa : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ (1 / 2 : ℝ)) :
    ∃ σ1 K : ℝ, 2 ≤ σ1 ∧ (∀ s : ℂ, σ1 ≤ s.re → ‖F s - 1‖ ≤ 1 / 2) ∧
      (∀ s : ℂ, σ1 ≤ s.re → ‖logDeriv F s‖ ≤ K) := by
  have hsum : ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (fun n => a n) s := fun s hs =>
    LSeriesSummable_of_le_const_mul_rpow hs ⟨Ca, fun n _ => by
      have := hCa n; convert this using 3; norm_num⟩
  have habs : LSeries.abscissaOfAbsConv (fun n => a n) ≤ (2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsum y (by simp only [Complex.ofReal_re]; linarith)
  set S : ℝ := ∑' n, ‖LSeries.term (fun n => a n) 2 n‖ with hS
  have hS2 : Summable fun n => ‖LSeries.term (fun n => a n) 2 n‖ :=
    summable_norm_iff.2 (hsum 2 (by norm_num))
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (2 * (S + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set σ1 : ℝ := 3 + k with hσ1
  -- logMul summability at σ1
  have hlm : LSeriesSummable (LSeries.logMul (fun n => a n)) (σ1 : ℂ) :=
    LSeriesSummable_logMul_of_lt_re (by
      simp only [Complex.ofReal_re]
      refine lt_of_le_of_lt habs ?_
      exact_mod_cast (show (2 : ℝ) < σ1 by
        rw [hσ1]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith))
  set K0 : ℝ := ∑' n, ‖LSeries.term (LSeries.logMul (fun n => a n)) (σ1 : ℂ) n‖ with hK0
  have hnear : ∀ s : ℂ, σ1 ≤ s.re → ‖F s - 1‖ ≤ 1 / 2 := by
    intro s hs
    have hs1 : 1 < s.re := by rw [hσ1] at hs; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
    have hsm : Summable (LSeries.term (fun n => a n) s) := hsum s (by linarith)
    rw [hF s hs1, LSeries, hsm.tsum_eq_add_tsum_ite 1]
    have h1 : LSeries.term (fun n => a n) s 1 = 1 := by simp [LSeries.term, ha1]
    rw [h1, add_sub_cancel_left]
    have hbound : ∀ n, ‖(if n = 1 then 0 else LSeries.term (fun n => a n) s n)‖ ≤
        (1 / 2) ^ k * ‖LSeries.term (fun n => a n) 2 n‖ := by
      intro n
      split_ifs with hn
      · simp
      · rcases Nat.lt_or_ge n 2 with h2 | h2
        · interval_cases n
          · simp
          · exact absurd rfl hn
        · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right (by omega), ite_eq_right (by
            omega)]
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
          simp only [Complex.re_ofNat]
          have hsplit : (n : ℝ) ^ s.re = (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (s.re - 2) := by
            rw [← Real.rpow_add hn0]; ring_nf
          have hpow : (2 : ℝ) ^ k ≤ (n : ℝ) ^ (s.re - 2) := by
            calc (2 : ℝ) ^ k ≤ (n : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hn2 k
              _ = (n : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
              _ ≤ (n : ℝ) ^ (s.re - 2) := by
                apply Real.rpow_le_rpow_of_exponent_le (by linarith)
                rw [hσ1] at hs; linarith
          rw [hsplit, div_le_iff₀ (by positivity)]
          have h2k : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
          have hA : 0 ≤ ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by positivity
          calc ‖a n‖ = ‖a n‖ / (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (2 : ℝ) := by field_simp
            _ = (1 / 2) ^ k * (‖a n‖ / (n : ℝ) ^ (2 : ℝ)) * ((n : ℝ) ^ (2 : ℝ) * 2 ^ k) := by
                rw [show (1 / 2 : ℝ) ^ k * (‖a n‖ / (n : ℝ) ^ (2 : ℝ)) * ((n : ℝ) ^ (2 : ℝ) *
                  2 ^ k) = ((1 / 2) ^ k * 2 ^ k) * (‖a n‖ / (n : ℝ) ^ (2 : ℝ) *
                  (n : ℝ) ^ (2 : ℝ)) by ring, h2k, one_mul]
            _ ≤ (1 / 2) ^ k * (‖a n‖ / (n : ℝ) ^ (2 : ℝ)) * ((n : ℝ) ^ (2 : ℝ) *
                (n : ℝ) ^ (s.re - 2)) := by gcongr
    have hsumR : Summable fun n => (1 / 2 : ℝ) ^ k * ‖LSeries.term (fun n => a n) 2 n‖ :=
      hS2.mul_left _
    calc ‖∑' n, (if n = 1 then 0 else LSeries.term (fun n => a n) s n)‖
        ≤ ∑' n, (1 / 2 : ℝ) ^ k * ‖LSeries.term (fun n => a n) 2 n‖ :=
          tsum_of_norm_bounded hsumR.hasSum hbound
      _ = (1 / 2) ^ k * S := by rw [tsum_mul_left]
      _ ≤ 1 / (2 * (S + 1)) * S := by gcongr
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨σ1, 2 * K0, by rw [hσ1]; linarith, hnear, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by rw [hσ1] at hs; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hFs : 1 / 2 ≤ ‖F s‖ := by
    have := hnear s hs
    have h := norm_sub_norm_le (1 : ℂ) (F s)
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hev : F =ᶠ[nhds s] LSeries (fun n => a n) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with u hu
    exact hF u hu
  have habs' : LSeries.abscissaOfAbsConv (fun n => a n) < s.re := by
    refine lt_of_le_of_lt habs ?_
    exact_mod_cast (show (2 : ℝ) < s.re by rw [hσ1] at hs; linarith)
  have hderiv : deriv F s = -LSeries (LSeries.logMul (fun n => a n)) s := by
    rw [hev.deriv_eq, LSeries_deriv habs']
  have hK : ‖LSeries (LSeries.logMul (fun n => a n)) s‖ ≤ K0 := by
    rw [LSeries]
    refine tsum_of_norm_bounded (summable_norm_iff.2 hlm).hasSum fun n => ?_
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n
  rw [logDeriv_apply, hderiv, norm_div, norm_neg, div_le_iff₀ (by linarith)]
  have hK0' : 0 ≤ K0 := tsum_nonneg fun _ => norm_nonneg _
  nlinarith

open Complex in
/-- Polynomial growth of `F` on the line `Re s = -1`, from the functional equation and Stirling. -/
private lemma exists_norm_le_mul_rpow_line_neg_one (F : ℂ → ℂ) (hFd : DifferentiableOn ℂ F {1}ᶜ) (D
    : FunctionalEquation F)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ s : ℂ, s.re = 2 → ‖F s‖ ≤ B) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ‖F (-1 + t * I)‖ ≤ C * |t| ^ (1 + ∑ i, 3 * D.α i) := by
  have hstir := fun i => Complex.exists_norm_Gamma_line_two_mul_inv_line_neg_one_le (D.α i) (D.α_pos
      i) (D.r i)
  choose M T hM0 hMT using hstir
  set T₀ : ℝ := 1 + ∑ i, |T i| with hT₀
  have hT : ∀ i, T i ≤ T₀ := fun i => by
    have := Finset.single_le_sum (f := fun i => |T i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := le_abs_self (T i)
    linarith
  have hfe := FunctionalEquation.eq_of_re_lt_one hFd D
  have hQ := D.Q_pos
  set A : ℝ := 1 + ∑ i, 3 * D.α i with hAdef
  have hsumα : 0 ≤ ∑ i, 3 * D.α i := Finset.sum_nonneg fun i _ => by
    have := D.α_pos i; positivity
  have hM : 0 ≤ ∏ i, M i := Finset.prod_nonneg fun i _ => hM0 i
  refine ⟨D.Q ^ 3 * B * (∏ i, M i), T₀, by positivity, ?_⟩
  intro t ht
  have ht1 : 1 ≤ |t| := by
    have : 0 ≤ ∑ i, |T i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have ht0 : 0 < |t| := by linarith
  set s : ℂ := -1 + t * I with hs
  have hs' : 1 - starRingEnd ℂ s = 2 + t * I := by
    apply Complex.ext
    · simp [s]; norm_num
    · simp [s]
  have hsre : s.re = -1 := by simp [s]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsre; simp at hsre
  have h := congrArg norm (hfe s (by rw [hsre]; norm_num) hs0)
  rw [hs'] at h
  simp only [norm_mul, Complex.norm_conj, D.norm_w, one_mul, norm_prod, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ] at h
  have h2re : (2 + t * I : ℂ).re = 2 := by simp
  rw [Complex.neg_re, hsre, h2re] at h
  set Pr := ∏ i, (‖Complex.Gamma (D.α i * (2 + t * I) + D.r i)‖ *
      ‖(Complex.Gamma (D.α i * (-1 + t * I) + D.r i))⁻¹‖) with hPr
  have hX : ‖F s‖ = D.Q ^ 3 * ‖F (2 + t * I)‖ * Pr := by
    rw [h, hPr, Finset.prod_mul_distrib]
    simp only [norm_inv]
    have hQm : D.Q ^ (-(-1 : ℝ)) = D.Q := by norm_num
    have hQ2 : D.Q ^ (2 : ℝ) = D.Q ^ 2 := Real.rpow_two _
    rw [hQm, hQ2]
    ring
  have hPrb : Pr ≤ (∏ i, M i) * |t| ^ A := by
    calc Pr ≤ ∏ i, (M i * |t| ^ (3 * D.α i)) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => hMT i t ((hT i).trans ht))
      _ = (∏ i, M i) * |t| ^ (∑ i, 3 * D.α i) := by
          rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos ht0]
      _ ≤ (∏ i, M i) * |t| ^ A := by
          gcongr
          linarith
  have hPr0 : 0 ≤ Pr := Finset.prod_nonneg fun i _ => by positivity
  have hF2 := hB (2 + t * I) h2re
  rw [hX]
  have : 0 < D.Q ^ 3 := by positivity
  calc D.Q ^ 3 * ‖F (2 + t * I)‖ * Pr ≤ D.Q ^ 3 * B * ((∏ i, M i) * |t| ^ A) := by
        gcongr
    _ = _ := by ring

open Complex in
/-- **Polynomial growth of `F` in the strip `-1 ≤ Re s ≤ σM`** (for `|Im s| ≥ 1`), from the two
edge bounds and Phragmén–Lindelöf applied to `G = (s - 1)^m F`. -/
private lemma exists_norm_le_mul_rpow_strip (F G : ℂ → ℂ) (m : ℕ) (β : ℝ) (hGd : Differentiable ℂ G)
    (hGo : HasGrowthOrderLE G β) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (hFd : DifferentiableOn ℂ F {1}ᶜ) (D : FunctionalEquation F) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ s : ℂ, s.re = 2 → ‖F s‖ ≤ B) (σM KM : ℝ) (hσM : 2 ≤ σM)
    (hKM : ∀ s : ℂ, s.re = σM → ‖F s‖ ≤ KM) :
    ∃ A C : ℝ, 0 ≤ A ∧
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ σM → 1 ≤ |s.im| → ‖F s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨C0, T₀, hC0, hleft⟩ := exists_norm_le_mul_rpow_line_neg_one F hFd D B hB0 hB
  set A0 : ℝ := 1 + ∑ i, 3 * D.α i with hA0
  have hsumα : 0 ≤ ∑ i, 3 * D.α i := Finset.sum_nonneg fun i _ => by
    have := D.α_pos i; positivity
  have hA0p : 1 ≤ A0 := by linarith
  set A : ℝ := m + A0 with hA
  have hKM0 : 0 ≤ KM := (norm_nonneg _).trans (hKM σM (by simp))
  obtain ⟨Bc, hBc⟩ := (isCompact_closedBall (0 : ℂ) (|T₀| + 2)).exists_bound_of_continuousOn
    hGd.continuous.continuousOn
  set CL : ℝ := max (max (3 ^ m * C0) |Bc|) ((σM + 1) ^ m * KM) with hCL
  have hCL0 : 0 ≤ CL := le_trans (abs_nonneg _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hpowA : ∀ t : ℝ, 1 ≤ |t| → (|t| ^ m * |t| ^ A0 = |t| ^ A) := by
    intro t ht
    have := Real.rpow_add (show (0:ℝ) < |t| by linarith) (m : ℝ) A0
    rw [Real.rpow_natCast] at this
    rw [hA, this]
  have hlines : ∃ C, ∀ s : ℂ, (s.re = -1 ∨ s.re = σM) → 1 ≤ |s.im| →
      ‖G s‖ ≤ C * |s.im| ^ A := by
    refine ⟨CL, fun s hs ht => ?_⟩
    have ht0 : 0 < |s.im| := by linarith
    have hpow1 : 1 ≤ |s.im| ^ A := Real.one_le_rpow ht (by positivity)
    have hs1 : s ≠ 1 := by
      rintro rfl; norm_num at ht
    rcases hs with hs | hs
    · have hse : s = -1 + (s.im : ℂ) * I := by
        apply Complex.ext <;> simp [hs]
      rcases le_or_gt T₀ |s.im| with hT0 | hT0
      · have hF := hleft s.im hT0
        rw [← hse] at hF
        have hn : ‖s - 1‖ ≤ 3 * |s.im| := by
          have := Complex.norm_le_abs_re_add_abs_im (s - 1)
          simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
            hs] at this
          norm_num at this
          linarith
        rw [hGF s hs1, norm_mul, norm_pow]
        calc ‖s - 1‖ ^ m * ‖F s‖ ≤ (3 * |s.im|) ^ m * (C0 * |s.im| ^ A0) := by gcongr
          _ = 3 ^ m * C0 * (|s.im| ^ m * |s.im| ^ A0) := by rw [mul_pow]; ring
          _ = 3 ^ m * C0 * |s.im| ^ A := by rw [hpowA _ ht]
          _ ≤ CL * |s.im| ^ A := by
            gcongr
            exact le_trans (le_max_left _ _) (le_max_left _ _)
      · have hmem : s ∈ Metric.closedBall (0 : ℂ) (|T₀| + 2) := by
          rw [mem_closedBall_zero_iff]
          have h1 := Complex.norm_le_abs_re_add_abs_im s
          rw [hs] at h1
          norm_num at h1
          have := le_abs_self T₀
          linarith
        calc ‖G s‖ ≤ Bc := hBc s hmem
          _ ≤ |Bc| := le_abs_self _
          _ ≤ CL := le_trans (le_max_right _ _) (le_max_left _ _)
          _ ≤ CL * |s.im| ^ A := le_mul_of_one_le_right hCL0 hpow1
    · have hn : ‖s - 1‖ ≤ (σM + 1) * |s.im| := by
        have := Complex.norm_le_abs_re_add_abs_im (s - 1)
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
          hs] at this
        rw [abs_of_nonneg (by linarith)] at this
        have h1 : σM ≤ σM * |s.im| := le_mul_of_one_le_right (by linarith) ht
        have e : (σM + 1) * |s.im| = σM * |s.im| + |s.im| := by ring
        rw [e]; linarith
      rw [hGF s hs1, norm_mul, norm_pow]
      have hmA : |s.im| ^ (m : ℝ) ≤ |s.im| ^ A :=
        Real.rpow_le_rpow_of_exponent_le ht (by rw [hA]; linarith)
      rw [Real.rpow_natCast] at hmA
      calc ‖s - 1‖ ^ m * ‖F s‖ ≤ ((σM + 1) * |s.im|) ^ m * KM := by
            gcongr
            exact hKM s hs
        _ = (σM + 1) ^ m * KM * |s.im| ^ m := by rw [mul_pow]; ring
        _ ≤ (σM + 1) ^ m * KM * |s.im| ^ A :=
          mul_le_mul_of_nonneg_left hmA (by positivity)
        _ ≤ CL * |s.im| ^ A := by
          gcongr
          exact le_max_right _ _
  obtain ⟨C, hC⟩ := PhragmenLindelof.vertical_strip_le_mul_rpow (f := G) (a := -1) (b := σM)
    (α := β + (|β| + 1) + 1) (A := A) hGd.diffContOnCl
    (hGo.exists_norm_le_exp_strip (-1) σM (by linarith)) hlines
  refine ⟨A, C, by rw [hA]; positivity, fun s h1 h2 ht => ?_⟩
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at ht
  have hn : 1 ≤ ‖s - 1‖ := le_trans ht (by simpa using Complex.abs_im_le_norm (s - 1))
  calc ‖F s‖ ≤ ‖G s‖ := by
        rw [hGF s hs1, norm_mul, norm_pow]
        exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hn)
    _ ≤ C * |s.im| ^ A := hC s h1 h2 ht

/-- From `|N(T) - c T log T| ≤ C T` at heights just above and just below every large `T`, and
monotonicity, `N(T) ~ c T log T`. -/
private lemma isEquivalent_of_abs_sub_le_mul (N : ℝ → ℝ) (c C T₀ : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hmono : ∀ T T' : ℝ, T ≤ T' → N T ≤ N T')
    (hbound : ∀ T : ℝ, T₀ ≤ T → ∃ T₁ ∈ Set.Ioo T (T + 1), ∃ T₂ ∈ Set.Ioo (T - 1) T,
      |N T₁ - c * T₁ * Real.log T₁| ≤ C * T₁ ∧ |N T₂ - c * T₂ * Real.log T₂| ≤ C * T₂) :
    Asymptotics.IsEquivalent Filter.atTop N (fun T => c * T * Real.log T) := by
  have hO : (fun T => N T - c * T * Real.log T) =O[Filter.atTop] (fun T : ℝ => T) := by
    refine Asymptotics.IsBigO.of_bound (3 * (c + C)) ?_
    filter_upwards [Filter.eventually_ge_atTop (max T₀ 3)] with T hT
    have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) hT
    have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
    obtain ⟨T₁, ⟨h11, h12⟩, T₂, ⟨h21, h22⟩, hb1, hb2⟩ := hbound T hT0
    have hN1 := hmono T T₁ h11.le
    have hN2 := hmono T₂ T h22.le
    rw [abs_le] at hb1 hb2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < T), abs_le]
    -- upper: c T₁ log T₁ ≤ c (T+1) log (T+1) ≤ c T log T + c (T + 1)
    have hlog1 : T₁ * Real.log T₁ ≤ T * Real.log T + (T + 1) := by
      have a1 : Real.log T₁ ≤ Real.log (T + 1) := Real.log_le_log (by linarith) h12.le
      have a2 : Real.log (T + 1) - Real.log T ≤ 1 / T := by
        rw [← Real.log_div (by linarith) (by linarith)]
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (T + 1) / T by positivity)
        have e : (T + 1) / T - 1 = 1 / T := by field_simp; ring
        linarith
      have a3 : Real.log (T + 1) ≤ T := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < T + 1 by linarith); linarith
      have hlT : 0 ≤ Real.log T₁ := Real.log_nonneg (by linarith)
      calc T₁ * Real.log T₁ ≤ (T + 1) * Real.log (T + 1) := by
            apply mul_le_mul h12.le a1 hlT (by linarith)
        _ = T * Real.log (T + 1) + Real.log (T + 1) := by ring
        _ ≤ T * (Real.log T + 1 / T) + T := by gcongr; linarith
        _ = T * Real.log T + 1 + T := by field_simp
        _ ≤ T * Real.log T + (T + 1) := by linarith
    have hlog2 : T * Real.log T - (T + 2) ≤ T₂ * Real.log T₂ := by
      have a1 : Real.log (T - 1) ≤ Real.log T₂ := Real.log_le_log (by linarith) h21.le
      have a2 : Real.log T - Real.log (T - 1) ≤ 1 / (T - 1) := by
        rw [← Real.log_div (by linarith) (by linarith)]
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < T / (T - 1) by
          apply div_pos <;> linarith)
        have e : T / (T - 1) - 1 = 1 / (T - 1) := by
          rw [div_sub_one (by linarith : (0:ℝ) < T - 1).ne']; congr 1; ring
        linarith
      have a3 : Real.log T ≤ T := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < T by linarith); linarith
      have hl : 0 ≤ Real.log (T - 1) := Real.log_nonneg (by linarith)
      have h1T : T * (1 / (T - 1)) ≤ 2 := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]; linarith
      calc T * Real.log T - (T + 2) ≤ T * (Real.log (T - 1) + 1 / (T - 1)) - (T + 2) := by
            gcongr; linarith
        _ = (T - 1) * Real.log (T - 1) + Real.log (T - 1) + T * (1 / (T - 1)) - (T + 2) := by
            ring
        _ ≤ (T - 1) * Real.log (T - 1) := by
            have : Real.log (T - 1) ≤ T := by
              have := Real.log_le_log (by linarith) (show T - 1 ≤ T by linarith); linarith
            linarith
        _ ≤ T₂ * Real.log T₂ := by
            apply mul_le_mul h21.le a1 hl (by linarith)
    have hCT1 : C * T₁ ≤ C * (T + 1) := by gcongr
    have hCT2 : C * T₂ ≤ C * T := by gcongr
    have e1 : c * T₁ * Real.log T₁ = c * (T₁ * Real.log T₁) := by ring
    have e2 : c * T₂ * Real.log T₂ = c * (T₂ * Real.log T₂) := by ring
    have hu := mul_le_mul_of_nonneg_left hlog1 hc.le
    have hl := mul_le_mul_of_nonneg_left hlog2 hc.le
    constructor <;> nlinarith
  have ho : (fun T : ℝ => T) =o[Filter.atTop] (fun T => c * T * Real.log T) := by
    have h1 : (fun T : ℝ => T * 1) =o[Filter.atTop] (fun T => T * Real.log T) :=
      (Asymptotics.isBigO_refl (fun T : ℝ => T) Filter.atTop).mul_isLittleO
        Real.isLittleO_const_log_atTop
    have h2 := h1.const_mul_right hc.ne'
    simp only [mul_one] at h2
    refine h2.congr_right fun T => ?_
    ring
  exact hO.trans_isLittleO ho

open Complex in
/-- The core estimate for positive degree: at heights `B` free of zeros of the completed
function (a dense set), `N(B) = (∑ α_i / π) B log B + O(B)`. -/
private lemma exists_abs_zeroCount_sub_le (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass) (F : ℂ
    → ℂ)
    (hF : IsLSeriesContinuation a F) (D : FunctionalEquation F) :
    ∃ (P : ℝ → Prop) (C B₀ : ℝ), 0 ≤ C ∧ (∀ T : ℝ, ∃ T' ∈ Set.Ioo T (T + 1), P T') ∧
      (∀ T : ℝ, {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T}.Finite) ∧
      ∀ B : ℝ, B₀ ≤ B → P B →
        |((∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ B},
          analyticOrderNatAt F ρ : ℕ) : ℝ) - (∑ i, D.α i) / Real.pi * B * Real.log B| ≤
          C * B := by
  classical
  obtain ⟨ha1, ⟨F₀, hF₀, ⟨m, G, β, hGd, hGo, hGF₀⟩, -⟩, ⟨b, θ, -, hlog, -⟩, hram⟩ := ha
  have hFF₀ : ∀ s, s ≠ 1 → F s = F₀ s := by
    have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have h3 : F =ᶠ[nhds (2 : ℂ)] F₀ := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
      rw [hF.1 s hs, hF₀.1 s hs]
    intro s hs
    exact (hF.2.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      (hF₀.2.analyticOnNhd hU) hpc (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) h3 hs
  have hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s := fun s hs => by
    rw [hFF₀ s hs]; exact hGF₀ s hs
  obtain ⟨Ca, hCa⟩ := hram (1 / 2) (by norm_num)
  obtain ⟨σ1, K, hσ1, hnear, hK⟩ := exists_norm_sub_one_le_and_norm_logDeriv_le a F hF.1 ha1 Ca hCa
  obtain ⟨B2, hB20, hB2⟩ := hF.exists_norm_le_of_re_eq_two hCa
  obtain ⟨Ag, Cg, hAg, hgrow⟩ := exists_norm_le_mul_rpow_strip F G m β hGd hGo hGF hF.2 D B2 hB20
      hB2 (2 * σ1)
    (3 / 2) (by linarith) (fun s hs => by
      have := hnear s (by rw [hs]; linarith)
      have h := norm_sub_norm_le (F s) 1
      rw [norm_one] at h
      linarith)
  obtain ⟨Kt, B₁, htop⟩ := exists_abs_im_integral_logDeriv_top_le_log F hF.2 σ1 hσ1 hnear Ag Cg hAg
      hgrow
  obtain ⟨H, hHd, hHrefl, hHr⟩ := exists_completed F G m hGd hGF D
  have hw0 : D.w ≠ 0 := by
    intro h; have := D.norm_w; rw [h, norm_zero] at this; norm_num at this
  have hFne1 : ∀ s : ℂ, 1 < s.re → F s ≠ 0 := by
    intro s hs
    rw [hF.1 s hs, (hlog.2 s hs).2]
    exact Complex.exp_ne_zero _
  have hHne1 : ∀ s : ℂ, 1 < s.re → H s ≠ 0 := by
    intro s hs
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    have hQ0 : (D.Q : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
    rw [hHr s (by linarith), hGF s hs1]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hs0)
      ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero hs0).mpr hQ0))
      (Finset.prod_ne_zero_iff.2 fun i _ => Complex.Gamma_ne_zero_of_re_pos ?_))
      (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hs1)) (hFne1 s hs))
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    have := D.α_pos i; have := D.r_re_nonneg i; nlinarith
  have hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1 := by
    intro s h0
    by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    rcases hcon with hlt | hgt
    · have hre : 1 < (1 - starRingEnd ℂ s).re := by simp; linarith
      have := hHrefl (1 - starRingEnd ℂ s)
      simp only [map_sub, map_one, Complex.conj_conj, sub_sub_cancel] at this
      rw [h0] at this
      exact mul_ne_zero hw0 ((map_ne_zero _).2 (hHne1 _ hre)) this.symm
    · exact hHne1 s hgt h0
  have hH2 : H 2 ≠ 0 := hHne1 2 (by norm_num)
  obtain ⟨A, hA1, hA0, hAz⟩ := exists_zero_free_bottom_height H hHd 2 hH2 hstrip
  have hAz' : ∀ s : ℂ, s.im = A → H s ≠ 0 := fun s hs h0 => hAz s h0 ⟨hs.ge, hs ▸ hA0⟩
  obtain ⟨CJ, BJ, hJ⟩ := abs_im_halfContour_logDeriv_completed_sub_le F G H m hF.2 hGF D hHr σ1 K Kt
      B₁ A hσ1 hnear hK htop
    hA1 hA0 hAz'
  -- the exceptional set
  set X : Finset ℂ := insert 0 (insert 1 (Finset.univ.image fun i => -D.r i / (D.α i : ℂ)))
    with hX
  set CX : ℝ := ∑ x ∈ X, ((analyticOrderNatAt F x : ℝ) + analyticOrderNatAt H x) with hCX
  have hCX0 : 0 ≤ CX := Finset.sum_nonneg fun _ _ => by positivity
  set S : ℝ → Set ℂ := fun T => {ρ : ℂ | 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T} with hS
  have heq : ∀ T, ∀ ρ ∈ S T, ρ ∉ X →
      ((F ρ = 0 ↔ H ρ = 0) ∧ analyticOrderNatAt F ρ = analyticOrderNatAt H ρ) := by
    intro T ρ hρ hρX
    have hρ0 : ρ ≠ 0 := fun h => hρX (by rw [h, hX]; exact Finset.mem_insert_self _ _)
    have hρ1 : ρ ≠ 1 := fun h => hρX (by
      rw [h, hX]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hpole : ∀ i, (D.α i : ℂ) * ρ + D.r i ≠ 0 := by
      intro i h
      apply hρX
      have hα : (D.α i : ℂ) ≠ 0 := by exact_mod_cast (D.α_pos i).ne'
      have : ρ = -D.r i / (D.α i : ℂ) := by field_simp; linear_combination h
      rw [this, hX]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    obtain ⟨h1, h2⟩ := completed_eq_zero_iff_and_analyticOrderAt_eq F G H m hF.2 hGd hGF D hHd hHr ρ
        hρ.1 hρ0 hρ1 hpole
    exact ⟨h1.symm, by simp only [analyticOrderNatAt, h2]⟩
  have hfinH : ∀ T, {ρ : ℂ | H ρ = 0 ∧ ρ ∈ S T}.Finite := by
    intro T
    refine (Complex.finite_setOf_eq_zero_norm_le hHd hH2 (1 + |T|)).subset fun ρ hρ => ⟨hρ.1, ?_⟩
    obtain ⟨h0, h1, h2, h3⟩ := hρ
    have := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at this
    have := (hstrip ρ h0).2
    have := le_abs_self T
    linarith
  have hfinF : ∀ T, {ρ : ℂ | F ρ = 0 ∧ ρ ∈ S T}.Finite := by
    intro T
    refine ((hfinH T).union X.finite_toSet).subset fun ρ hρ => ?_
    by_cases hρX : ρ ∈ X
    · exact Or.inr hρX
    · exact Or.inl ⟨(heq T ρ hρ.2 hρX).1.1 hρ.1, hρ.2⟩
  have hcmp : ∀ T, |((∑ᶠ ρ ∈ {ρ | F ρ = 0 ∧ ρ ∈ S T}, analyticOrderNatAt F ρ : ℕ) : ℝ) -
      ((∑ᶠ ρ ∈ {ρ | H ρ = 0 ∧ ρ ∈ S T}, analyticOrderNatAt H ρ : ℕ) : ℝ)| ≤ CX :=
    fun T => abs_sub_zeroCount_le_of_eq_off_finset F H X (S T) (hfinF T) (hfinH T) (heq T)
  refine ⟨fun B => ∀ s : ℂ, s.im = B → H s ≠ 0, CX + |CJ| / Real.pi, max BJ 1,
    by positivity, fun T => exists_zero_free_height H hHd 2 hH2 hstrip T, hfinF, ?_⟩
  intro B hB hBz
  have hB1 : 1 ≤ B := le_trans (le_max_right _ _) hB
  have hBJ : BJ ≤ B := le_trans (le_max_left _ _) hB
  have hNH := pi_mul_zeroCount_eq_im_halfContour H D.w hHd hw0 hHrefl hstrip hH2 σ1 A B (by
      linarith) hA0 hAz
    (by linarith) hBz
  have hJB := hJ B hBJ hBz
  rw [← hNH] at hJB
  have hc := hcmp B
  set NF := ((∑ᶠ ρ ∈ {ρ | F ρ = 0 ∧ ρ ∈ S B}, analyticOrderNatAt F ρ : ℕ) : ℝ)
  set NH := ((∑ᶠ ρ ∈ {ρ | H ρ = 0 ∧ ρ ∈ S B}, analyticOrderNatAt H ρ : ℕ) : ℝ)
  have hpi := Real.pi_pos
  have hNHb : |NH - (∑ i, D.α i) / Real.pi * B * Real.log B| ≤ |CJ| / Real.pi * B := by
    have e : NH - (∑ i, D.α i) / Real.pi * B * Real.log B =
        (Real.pi * NH - (∑ i, D.α i) * B * Real.log B) / Real.pi := by
      field_simp
    rw [e, abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    have : CJ * B ≤ |CJ| * B := by gcongr; exact le_abs_self CJ
    calc |Real.pi * NH - (∑ i, D.α i) * B * Real.log B| ≤ CJ * B := hJB
      _ ≤ |CJ| * B := this
      _ = |CJ| / Real.pi * B * Real.pi := by field_simp
  change |NF - (∑ i, D.α i) / Real.pi * B * Real.log B| ≤ (CX + |CJ| / Real.pi) * B
  have hCXB : CX ≤ CX * B := le_mul_of_one_le_right hCX0 hB1
  rw [abs_le] at hc hNHb ⊢
  constructor <;> nlinarith

/-- The zero count is monotone in the height. -/
private lemma zeroCount_mono (F : ℂ → ℂ)
    (hfin : ∀ T : ℝ, {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T}.Finite) (T T' : ℝ)
    (hTT : T ≤ T') :
    ((∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T}, analyticOrderNatAt F ρ : ℕ) : ℝ) ≤
      ((∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T'},
        analyticOrderNatAt F ρ : ℕ) : ℝ) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin T), finsum_mem_eq_finite_toFinset_sum _ (hfin T')]
  exact_mod_cast Finset.sum_le_sum_of_subset (fun ρ hρ => by
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans hTT⟩)

/-- **Selberg's zero-counting theorem.** For `a` in the Selberg class with continuation `F` and
any functional equation `D` of `F`, the number `N(T)` of zeros `ρ` of `F` with `0 ≤ Re ρ` and
`0 ≤ Im ρ ≤ T`, counted with multiplicity, satisfies `N(T) ∼ (deg D) T log T / 2π` as
`T → ∞`. -/
theorem isEquivalent_zeroCount (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass) (F : ℂ → ℂ)
    (hF : IsLSeriesContinuation a F) (D : FunctionalEquation F) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun T : ℝ => ((∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T},
        analyticOrderNatAt F ρ : ℕ) : ℝ))
      (fun T : ℝ => D.degree * T * Real.log T / (2 * Real.pi)) := by
  by_cases hD0 : D.degree = 0
  · have e1 : (fun T : ℝ => ((∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T},
        analyticOrderNatAt F ρ : ℕ) : ℝ)) = fun _ => 0 := by
      funext T; rw [zeroCount_eq_zero_of_degree_eq_zero a ha F hF D hD0 T]; simp
    have e2 : (fun T : ℝ => D.degree * T * Real.log T / (2 * Real.pi)) = fun _ => 0 := by
      funext T; rw [hD0]; simp
    rw [e1, e2]
  have hsum : 0 < ∑ i, D.α i := by
    have h0 : 0 ≤ ∑ i, D.α i := Finset.sum_nonneg fun i _ => (D.α_pos i).le
    refine lt_of_le_of_ne h0 fun h => hD0 ?_
    simp only [FunctionalEquation.degree, ← h, mul_zero]
  obtain ⟨P, C, B₀, hC, hdense, hfin, hbd⟩ := exists_abs_zeroCount_sub_le a ha F hF D
  have hc : 0 < (∑ i, D.α i) / Real.pi := div_pos hsum Real.pi_pos
  have key := isEquivalent_of_abs_sub_le_mul _ ((∑ i, D.α i) / Real.pi) C (B₀ + 1) hc hC
      (zeroCount_mono F hfin)
    (fun T hT => by
      obtain ⟨T₁, hT₁, hP₁⟩ := hdense T
      obtain ⟨T₂, hT₂, hP₂⟩ := hdense (T - 1)
      rw [sub_add_cancel] at hT₂
      exact ⟨T₁, hT₁, T₂, hT₂, hbd T₁ (by linarith [hT₁.1]) hP₁,
        hbd T₂ (by linarith [hT₂.1]) hP₂⟩)
  refine key.congr_right (Filter.Eventually.of_forall fun T => ?_)
  simp only [FunctionalEquation.degree]
  field_simp

end SelbergClass
