/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.RootsOfUnity.Complex
import MathlibExt.Analysis.Complex.Hurwitz
import MathlibExt.Analysis.Complex.NormalFamilies

namespace MathlibExt.Analysis.Complex.RiemannMappingWanted

open Filter Metric Set
open scoped Topology

/-- The disc automorphism `w ↦ (w - a) / (1 - ā w)`. -/
private noncomputable def rmap_mob (a w : ℂ) : ℂ := (w - a) / (1 - starRingEnd ℂ a * w)

/-- The extremal family: holomorphic injective maps `U → ball 0 1` sending `z₀` to `0`. -/
private def rmap_Fam (U : Set ℂ) (z₀ : ℂ) : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f U ∧ Set.InjOn f U ∧ Set.MapsTo f U (ball 0 1) ∧ f z₀ = 0}

/-- Simply connected sets are preconnected. -/
private lemma rmap_isPreconnected {U : Set ℂ} (h : IsSimplyConnected U) :
    IsPreconnected U :=
  h.isPathConnected.isConnected.isPreconnected

/-- A continuous square root of a holomorphic function is holomorphic away from zeros. -/
private lemma rmap_hasDerivAt_sqrt {U : Set ℂ} (hUo : IsOpen U) {G s : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G U) (hs : ContinuousOn s U)
    (hsq : ∀ z ∈ U, s z ^ 2 = G z) {x : ℂ} (hx : x ∈ U) (hsx : s x ≠ 0) :
    HasDerivAt s (deriv G x / (2 * s x)) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hGdiff : DifferentiableAt ℂ G x := hG.differentiableAt (hUo.mem_nhds hx)
  have hGslope : Tendsto (slope G x) (𝓝[≠] x) (𝓝 (deriv G x)) :=
    hasDerivAt_iff_tendsto_slope.mp hGdiff.hasDerivAt
  have hscont : ContinuousAt s x := hs.continuousAt (hUo.mem_nhds hx)
  have hsum : Tendsto (fun y => s y + s x) (𝓝[≠] x) (𝓝 (2 * s x)) := by
    have h1 : Tendsto (fun y => s y + s x) (𝓝 x) (𝓝 (s x + s x)) :=
      hscont.add continuousAt_const
    have h2 : s x + s x = 2 * s x := by ring
    rw [h2] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hne : (2 : ℂ) * s x ≠ 0 := mul_ne_zero (by norm_num) hsx
  have hev : ∀ᶠ y in 𝓝[≠] x, s y + s x ≠ 0 := hsum.eventually_ne hne
  have hdiv : Tendsto (fun y => slope G x y / (s y + s x)) (𝓝[≠] x)
      (𝓝 (deriv G x / (2 * s x))) :=
    hGslope.div hsum hne
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s := ({x}ᶜ : Set ℂ)),
    mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hx), hev] with y hyx hyU hysum
  have hyx' : y ≠ x := hyx
  have hGy : G y - G x = (s y - s x) * (s y + s x) := by
    rw [← hsq y hyU, ← hsq x hx]; ring
  rw [slope_def_field, slope_def_field, hGy]
  have hyx0 : y - x ≠ 0 := sub_ne_zero.mpr hyx'
  field_simp

/-- On a simply connected open set, a nonvanishing holomorphic function has a
holomorphic square root. -/
private lemma rmap_exists_holo_sqrt {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G U)
    (hG0 : ∀ z ∈ U, G z ≠ 0) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s U ∧ ∀ z ∈ U, s z ^ 2 = G z := by
  have hcont : ContinuousOn G U := hG.continuousOn
  have hU0 : (0 : ℂ) ∉ G '' U := by
    rintro ⟨z, hzU, hGz⟩
    exact hG0 z hzU hGz
  obtain ⟨s, hsc, hsq⟩ :=
    Complex.exists_continuousOn_pow_eq hUc hUo hcont hU0 (by norm_num : 2 ≠ 0)
  refine ⟨s, fun z hz => ?_, fun z hz => hsq z⟩
  have hsz : s z ≠ 0 := by
    intro h0
    have h1 := hsq z
    rw [h0] at h1
    simp only [zero_pow (by norm_num : 2 ≠ 0)] at h1
    exact hG0 z hz h1.symm
  have hder : HasDerivAt s (deriv G z / (2 * s z)) z :=
    rmap_hasDerivAt_sqrt hUo hG hsc (fun w _ => hsq w) hz hsz
  exact hder.differentiableAt.differentiableWithinAt

/-- The square root of `z - a` for `a ∉ U`: injective, strictly differentiable,
and its image avoids its own negation. -/
private lemma rmap_sqrt_sub {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) {a : ℂ} (ha : a ∉ U) :
    ∃ s : ℂ → ℂ, (∀ z : ℂ, s z ^ 2 = z - a) ∧ Function.Injective s ∧
      (∀ z ∈ U, s z ≠ 0) ∧ (∀ z ∈ U, HasStrictDerivAt s (2 * s z)⁻¹ z) ∧
      (∀ z ∈ U, ∀ w ∈ U, s z ≠ -s w) := by
  have hcont : ContinuousOn (fun z : ℂ => z - a) U :=
    continuousOn_id.sub continuousOn_const
  have hU0 : (0 : ℂ) ∉ (fun z : ℂ => z - a) '' U := by
    rintro ⟨z, hzU, hza⟩
    have hza' : z - a = 0 := hza
    exact ha (sub_eq_zero.mp hza' ▸ hzU)
  obtain ⟨s, hsc, hsq⟩ :=
    Complex.exists_continuousOn_pow_eq hUc hUo hcont hU0 (by norm_num : 2 ≠ 0)
  have hinj : Function.Injective s := by
    intro z w hzw
    have hz := hsq z
    have hw := hsq w
    have h3 : z - a = w - a := by rw [← hz, ← hw, hzw]
    have h4 : z - a + a = w - a + a := congrArg (· + a) h3
    rwa [sub_add_cancel, sub_add_cancel] at h4
  have hne : ∀ z ∈ U, s z ≠ 0 := by
    intro z hz h0
    have h1 := hsq z
    rw [h0] at h1
    simp only [zero_pow (by norm_num : 2 ≠ 0)] at h1
    have h2 : z = a := sub_eq_zero.mp h1.symm
    exact ha (h2 ▸ hz)
  have hderiv : ∀ z ∈ U, HasStrictDerivAt s (2 * s z)⁻¹ z := by
    intro z hz
    have hpow : HasStrictDerivAt (fun w : ℂ => w ^ 2) (2 * s z) (s z) := by
      have h := hasStrictDerivAt_pow 2 (s z)
      simpa using h
    have h2 : HasStrictDerivAt (fun w : ℂ => w ^ 2 + a) (2 * s z) (s z) :=
      hpow.add_const a
    have hne' : (2 : ℂ) * s z ≠ 0 := mul_ne_zero (by norm_num) (hne z hz)
    have hfg : ∀ᶠ y in 𝓝 z, (fun w : ℂ => w ^ 2 + a) (s y) = y :=
      Filter.Eventually.of_forall fun y => by
        change s y ^ 2 + a = y
        rw [hsq y, sub_add_cancel]
    exact HasStrictDerivAt.of_local_left_inverse
      (hsc.continuousAt (hUo.mem_nhds hz)) h2 hne' hfg
  have hanti : ∀ z ∈ U, ∀ w ∈ U, s z ≠ -s w := by
    intro z hz w hw hcon
    have hz2 := hsq z
    have hw2 := hsq w
    have h3 : z - a = w - a := by rw [← hz2, ← hw2, hcon]; ring
    have h4 : z - a + a = w - a + a := congrArg (· + a) h3
    have hzw : z = w := by rwa [sub_add_cancel, sub_add_cancel] at h4
    subst hzw
    have hzero : s z = 0 := by linear_combination hcon / 2
    exact hne z hz hzero
  exact ⟨s, hsq, hinj, hne, hderiv, hanti⟩

/-- The extremal family is nonempty. -/
private lemma rmap_fam_nonempty {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ f₀ : ℂ → ℂ, f₀ ∈ rmap_Fam U z₀ := by
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).mp hU
  obtain ⟨s, hsq, hinj, hne, hderiv, hanti⟩ := rmap_sqrt_sub hUo hUc ha
  have hsdiff : DifferentiableOn ℂ s U := fun z hz =>
    (hderiv z hz).hasDerivAt.differentiableAt.differentiableWithinAt
  have hne0 : (2 : ℂ) * s z₀ ≠ 0 := mul_ne_zero (by norm_num) (hne z₀ hz₀)
  have hmeq : map s (𝓝 z₀) = 𝓝 (s z₀) :=
    (hderiv z₀ hz₀).map_nhds_eq (inv_ne_zero hne0)
  have hmap : s '' U ∈ 𝓝 (s z₀) := by
    rw [← hmeq]
    exact Filter.image_mem_map (hUo.mem_nhds hz₀)
  obtain ⟨r, hr0, hrsub⟩ := Metric.mem_nhds_iff.mp hmap
  have hlb : ∀ z ∈ U, r ≤ ‖s z + s z₀‖ := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hmem : -s z ∈ ball (s z₀) r := by
      rw [Metric.mem_ball]
      have he : dist (-s z) (s z₀) = ‖s z + s z₀‖ := by
        rw [dist_eq_norm]
        have e : -s z - s z₀ = -(s z + s z₀) := by abel
        rw [e, norm_neg]
      rw [he]
      exact hlt
    obtain ⟨w, hwU, hws⟩ := hrsub hmem
    exact hanti w hwU z hz hws
  have hsum0 : ∀ z ∈ U, s z + s z₀ ≠ 0 := by
    intro z hz h0
    have h2 := hlb z hz
    rw [h0, norm_zero] at h2
    exact absurd h2 (not_le.mpr hr0)
  have hr04 : (0 : ℝ) < r / 4 := by positivity
  have hr0ne : r ≠ 0 := ne_of_gt hr0
  set c : ℂ := ((r / 4 : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr04)
  have hden : DifferentiableOn ℂ (fun z : ℂ => s z + s z₀) U :=
    hsdiff.add (differentiableOn_const (s z₀))
  have hFdiff : DifferentiableOn ℂ (fun z : ℂ => c / (s z + s z₀)) U :=
    (differentiableOn_const c).div hden hsum0
  have hc_norm : ‖c‖ = r / 4 := by
    rw [hc, Complex.norm_real, Real.norm_of_nonneg hr04.le]
  have hnorm : ∀ z ∈ U, ‖c / (s z + s z₀)‖ ≤ 1 / 4 := by
    intro z hz
    rw [Complex.norm_div, hc_norm]
    have h2 := hlb z hz
    have hpos : 0 < ‖s z + s z₀‖ := lt_of_lt_of_le hr0 h2
    calc (r / 4) / ‖s z + s z₀‖ ≤ (r / 4) / r :=
            div_le_div_of_nonneg_left hr04.le hr0 h2
        _ = 1 / 4 := by
            rw [div_eq_iff hr0ne]
            ring
  refine ⟨fun z => c / (s z + s z₀) - c / (s z₀ + s z₀), hFdiff.sub_const _,
    ?_, ?_, sub_self _⟩
  · intro z hz w hw heq
    have hFw : c / (s z + s z₀) = c / (s w + s z₀) := by
      have h := congrArg (· + c / (s z₀ + s z₀)) heq
      simpa using h
    have hsw : s z + s z₀ = s w + s z₀ := by
      have h := (div_eq_div_iff (hsum0 z hz) (hsum0 w hw)).mp hFw
      have h2 := mul_left_cancel₀ hc0 h
      exact h2.symm
    have hzw : s z = s w := add_right_cancel hsw
    exact hinj hzw
  · intro z hz
    have hle : ‖c / (s z + s z₀) - c / (s z₀ + s z₀)‖ < 1 :=
      calc ‖c / (s z + s z₀) - c / (s z₀ + s z₀)‖
            ≤ ‖c / (s z + s z₀)‖ + ‖c / (s z₀ + s z₀)‖ := norm_sub_le _ _
          _ ≤ 1 / 4 + 1 / 4 := add_le_add (hnorm z hz) (hnorm z₀ hz₀)
          _ < 1 := by norm_num
    simpa [Metric.mem_ball, dist_zero_right] using hle

/-- Key norm-square identity for the disc automorphism. -/
private lemma rmap_mob_normSq_key (a w : ℂ) :
    Complex.normSq (1 - starRingEnd ℂ a * w) - Complex.normSq (w - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq w) := by
  rw [starRingEnd_apply]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The Möbius denominator is nonzero on the disc. -/
private lemma rmap_mob_den {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 - starRingEnd ℂ a * w ≠ 0 := by
  have hn : ‖starRingEnd ℂ a‖ = ‖a‖ := by
    rw [starRingEnd_apply, Complex.star_def]
    exact RCLike.norm_conj a
  have h : ‖starRingEnd ℂ a * w‖ < 1 := by
    rw [norm_mul, hn]
    calc ‖a‖ * ‖w‖ ≤ 1 * ‖w‖ :=
            mul_le_mul_of_nonneg_right (le_of_lt ha) (norm_nonneg _)
        _ = ‖w‖ := one_mul _
        _ < 1 := hw
  intro hcon
  have h1 : starRingEnd ℂ a * w = 1 := (sub_eq_zero.mp hcon).symm
  have h2 : ‖starRingEnd ℂ a * w‖ = 1 := by rw [h1, norm_one]
  linarith

/-- The Möbius map sends the disc to itself. -/
private lemma rmap_mob_maps {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖rmap_mob a w‖ < 1 := by
  have hden := rmap_mob_den ha hw
  have hkey := rmap_mob_normSq_key a w
  have ha1 : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_lt_one_iff₀ (norm_nonneg _)).mpr ha
  have hw1 : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_lt_one_iff₀ (norm_nonneg _)).mpr hw
  have hlt : Complex.normSq (w - a)
      < Complex.normSq (1 - starRingEnd ℂ a * w) := by
    have hpos : 0 < (1 - Complex.normSq a) * (1 - Complex.normSq w) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have hnorm : ‖w - a‖ < ‖1 - starRingEnd ℂ a * w‖ := by
    by_contra hcon
    push Not at hcon
    have hle : ‖1 - starRingEnd ℂ a * w‖ ^ 2 ≤ ‖w - a‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hcon 2
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at hle
    linarith
  have hpos2 : 0 < ‖1 - starRingEnd ℂ a * w‖ := norm_pos_iff.mpr hden
  unfold rmap_mob
  rw [Complex.norm_div, div_lt_one hpos2]
  exact hnorm

/-- The Möbius map is inverted by negating the parameter. -/
private lemma rmap_mob_inv {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    rmap_mob (-a) (rmap_mob a w) = w := by
  have hden := rmap_mob_den ha hw
  have hmem : ‖rmap_mob a w‖ < 1 := rmap_mob_maps ha hw
  set u : ℂ := rmap_mob a w with hu_def
  have hmem' : ‖u‖ < 1 := hmem
  have hden2 := rmap_mob_den (by rwa [norm_neg] : ‖-a‖ < 1) hmem'
  have estar : starRingEnd ℂ (-a) = -starRingEnd ℂ a := map_neg _ _
  have hu : u * (1 - starRingEnd ℂ a * w) = w - a := by
    rw [hu_def]
    unfold rmap_mob
    exact div_mul_cancel₀ _ hden
  unfold rmap_mob
  rw [div_eq_iff hden2, estar]
  linear_combination hu

/-- The Möbius map vanishes exactly at `a`. -/
private lemma rmap_mob_eq_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    rmap_mob a w = 0 ↔ w = a := by
  have hden := rmap_mob_den ha hw
  unfold rmap_mob
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact sub_eq_zero.mp h
    · exact absurd h hden
  · intro h
    left
    exact sub_eq_zero.mpr h

/-- Values of the Möbius map at `0` and at `a`. -/
private lemma rmap_mob_zero (a : ℂ) : rmap_mob a 0 = -a := by
  unfold rmap_mob
  simp

/-- The Möbius map sends `a` to `0`. -/
private lemma rmap_mob_self (a : ℂ) : rmap_mob a a = 0 := by
  unfold rmap_mob
  simp

/-- The Möbius map is injective on the disc. -/
private lemma rmap_mob_injOn {a : ℂ} (ha : ‖a‖ < 1) :
    Set.InjOn (rmap_mob a) (ball 0 1) := by
  intro x hx y hy hxy
  have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hy' : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hy
  have h1 : rmap_mob (-a) (rmap_mob a x) = rmap_mob (-a) (rmap_mob a y) := by
    rw [hxy]
  rw [rmap_mob_inv ha hx', rmap_mob_inv ha hy'] at h1
  exact h1

/-- Derivative of the Möbius map. -/
private lemma rmap_mob_hasDerivAt (a w : ℂ)
    (hw : 1 - starRingEnd ℂ a * w ≠ 0) :
    HasDerivAt (rmap_mob a)
      ((1 - starRingEnd ℂ a * a) / (1 - starRingEnd ℂ a * w) ^ 2) w := by
  have hnum : HasDerivAt (fun z : ℂ => z - a) 1 w := by
    have e := (hasDerivAt_id w).sub (hasDerivAt_const w a)
    rw [show (1 : ℂ) - 0 = 1 from sub_zero 1] at e
    exact e
  have hden : HasDerivAt (fun z : ℂ => 1 - starRingEnd ℂ a * z)
      (-starRingEnd ℂ a) w := by
    have h := HasDerivAt.const_sub 1
      (HasDerivAt.const_mul (starRingEnd ℂ a) (hasDerivAt_id w))
    simpa using h
  have h := hnum.div hden hw
  have heq : rmap_mob a = fun z : ℂ => (z - a) / (1 - starRingEnd ℂ a * z) := rfl
  rw [heq]
  refine h.congr_deriv ?_
  ring

/-- The Möbius map is holomorphic on the disc. -/
private lemma rmap_mob_diffOn {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (rmap_mob a) (ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  exact (rmap_mob_hasDerivAt a w (rmap_mob_den ha hw')).differentiableAt.differentiableWithinAt

/-- Local normal form: a holomorphic function vanishing to order at least two is
locally an `n`-th power of a function with nonzero strict derivative. -/
private lemma rmap_local_power {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a)
    (hg0 : g a = 0) (hg1 : deriv g a = 0) (hne : ¬ ∀ᶠ z in 𝓝 a, g z = 0) :
    ∃ n : ℕ, ∃ k : ℂ → ℂ, ∃ κ : ℂ, 2 ≤ n ∧ k a = 0 ∧ κ ≠ 0 ∧
      HasStrictDerivAt k κ a ∧ ∀ᶠ z in 𝓝 a, g z = k z ^ n := by
  obtain ⟨n, u, hu_an, hu_ne, heq⟩ :=
    hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h0 := heq.self_of_nhds
    rw [hg0, pow_zero, one_smul] at h0
    exact hu_ne h0.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hucont : ContinuousAt u a := hu_an.differentiableAt.continuousAt
    have hlim : Tendsto u (𝓝[≠] a) (𝓝 (u a)) :=
      hucont.mono_left nhdsWithin_le_nhds
    have hslope : Tendsto (slope g a) (𝓝[≠] a) (𝓝 (u a)) := by
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin (s := ({a}ᶜ : Set ℂ)),
        mem_nhdsWithin_of_mem_nhds heq] with z hzne hz
      rw [slope_def_field, hz, hg0]
      have hza : z - a ≠ 0 := sub_ne_zero.mpr hzne
      field_simp; ring
    have hderiv : HasDerivAt g (u a) a := hasDerivAt_iff_tendsto_slope.mpr hslope
    have hval : deriv g a = u a := hderiv.deriv
    rw [hg1] at hval
    exact hu_ne hval.symm
  have hn2 : 2 ≤ n := by omega
  obtain ⟨c, hcn, hc0⟩ : ∃ c : ℂ, c ^ n = u a ∧ c ≠ 0 := by
    have h1 : (u a ^ ((n : ℂ))⁻¹) ^ n = u a := Complex.cpow_nat_inv_pow _ hn0
    refine ⟨u a ^ ((n : ℂ))⁻¹, h1, ?_⟩
    intro hcon
    apply hu_ne
    rw [← h1, hcon, zero_pow hn0]
  have hq_an : AnalyticAt ℂ (u / fun _ => u a) a :=
    hu_an.div analyticAt_const hu_ne
  have hq_an' : AnalyticAt ℂ (fun z => u z / u a) a := hq_an
  have hexp_an : AnalyticAt ℂ (fun _ : ℂ => ((n : ℂ))⁻¹) a := analyticAt_const
  have hpow_an : AnalyticAt ℂ (fun z => (u z / u a) ^ ((n : ℂ))⁻¹) a := by
    apply hq_an'.cpow hexp_an
    rw [div_self hu_ne]
    exact Complex.one_mem_slitPlane
  have hv_an : AnalyticAt ℂ (fun z => c * ((u z / u a) ^ ((n : ℂ))⁻¹)) a :=
    (analyticAt_const (v := c)).mul hpow_an
  have hva : c * ((u a / u a) ^ ((n : ℂ))⁻¹) = c := by
    rw [div_self hu_ne, Complex.one_cpow, mul_one]
  have hvn : ∀ z : ℂ, (c * ((u z / u a) ^ ((n : ℂ))⁻¹)) ^ n = u z := by
    intro z
    have h1 : (((u z / u a) : ℂ) ^ ((n : ℂ))⁻¹) ^ n = u z / u a :=
      Complex.cpow_nat_inv_pow _ hn0
    rw [mul_pow, h1, hcn, mul_comm (u a), div_mul_cancel₀ _ hu_ne]
  have hsub_an : AnalyticAt ℂ (fun z : ℂ => z - a) a :=
    (differentiable_id.sub_const a).analyticAt a
  have hk_an : AnalyticAt ℂ
      (fun z => (z - a) * (c * ((u z / u a) ^ ((n : ℂ))⁻¹))) a :=
    hsub_an.mul hv_an
  have hderiv_k : HasDerivAt
      (fun z => (z - a) * (c * ((u z / u a) ^ ((n : ℂ))⁻¹))) c a := by
    have hvcont : ContinuousAt (fun z => c * ((u z / u a) ^ ((n : ℂ))⁻¹)) a :=
      hv_an.differentiableAt.continuousAt
    have hva' : (fun z => c * ((u z / u a) ^ ((n : ℂ))⁻¹)) a = c := hva
    have hlim : Tendsto (fun z => c * ((u z / u a) ^ ((n : ℂ))⁻¹)) (𝓝[≠] a)
        (𝓝 c) := by
      simpa [hva'] using hvcont.mono_left nhdsWithin_le_nhds
    rw [hasDerivAt_iff_tendsto_slope]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin (s := ({a}ᶜ : Set ℂ))] with z hzne
    have hza : z - a ≠ 0 := sub_ne_zero.mpr hzne
    rw [slope_def_field, sub_self, zero_mul, sub_zero, eq_div_iff hza]
    ring
  have hstrict : HasStrictDerivAt
      (fun z => (z - a) * (c * ((u z / u a) ^ ((n : ℂ))⁻¹))) c a := by
    have h := hk_an.hasStrictDerivAt
    rw [show deriv (fun z => (z - a) * (c * ((u z / u a) ^ ((n : ℂ))⁻¹))) a
      = c from hderiv_k.deriv] at h
    exact h
  refine ⟨n, fun z => (z - a) * (c * ((u z / u a) ^ ((n : ℂ))⁻¹)), c,
    hn2, by simp, hc0, hstrict, ?_⟩
  filter_upwards [heq] with z hz
  simp only [hz, smul_eq_mul, mul_pow, hvn z]

/-- A holomorphic injective map has nonzero derivative. -/
private lemma rmap_deriv_ne_zero_of_injOn {U : Set ℂ} (hUo : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {a : ℂ} (ha : a ∈ U) : deriv f a ≠ 0 := by
  by_contra hcon
  have hg_an : AnalyticAt ℂ (fun z => f z - f a) a :=
    (hf.analyticAt (hUo.mem_nhds ha)).sub (analyticAt_const (v := f a))
  have hg0 : (fun z => f z - f a) a = 0 := sub_self _
  have hg1 : deriv (fun z => f z - f a) a = 0 := by
    rw [deriv_sub_const]
    exact hcon
  have hnev : ¬ ∀ᶠ z in 𝓝 a, (fun z => f z - f a) z = 0 := by
    intro hev
    have hUev : U ∈ 𝓝 a := hUo.mem_nhds ha
    obtain ⟨ε, hε0, hεsub⟩ :=
      Metric.mem_nhds_iff.mp (Filter.inter_mem hev hUev)
    set e : ℂ := ((ε / 2 : ℝ) : ℂ) with he
    have he0 : e ≠ 0 := by
      rw [he]
      exact Complex.ofReal_ne_zero.mpr (half_pos hε0).ne'
    have hxa : a + e ∈ ball a ε := by
      rw [Metric.mem_ball]
      have hde : dist (a + e) a = ‖e‖ := by
        rw [dist_eq_norm, add_sub_cancel_left]
      rw [hde, he, Complex.norm_real,
        Real.norm_of_nonneg (half_pos hε0).le]
      linarith
    have hxU : a + e ∈ U := (hεsub hxa).2
    have hgx : f (a + e) - f a = 0 := (hεsub hxa).1
    have hfeq : f (a + e) = f a := by linear_combination hgx
    have hne' : a + e ≠ a := by
      intro hcc
      apply he0
      have hcc2 : a + e - a = a - a := congrArg (· - a) hcc
      rw [add_sub_cancel_left, sub_self] at hcc2
      exact hcc2
    exact hne' (hinj hxU ha hfeq)
  obtain ⟨n, k, κ, hn2, hk0, hκ, hstrict, hkeq⟩ :=
    rmap_local_power hg_an hg0 hg1 hnev
  have hmap : map k (𝓝 a) = 𝓝 (k a) := hstrict.map_nhds_eq hκ
  rw [hk0] at hmap
  have hkS : k '' (U ∩ {z | (fun z => f z - f a) z = k z ^ n}) ∈ map k (𝓝 a) :=
    Filter.image_mem_map (Filter.inter_mem (hUo.mem_nhds ha) hkeq)
  rw [hmap] at hkS
  obtain ⟨r, hr0, hrsub⟩ := Metric.mem_nhds_iff.mp hkS
  have hn0' : n ≠ 0 := by omega
  have hn1' : 1 < n := by omega
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))) n :=
    Complex.isPrimitiveRoot_exp n hn0'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) with hζdef
  have hζn : ζ ^ n = 1 := hprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hprim.ne_one hn1'
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζn hn0'
  set t : ℂ := ((r / 2 : ℝ) : ℂ) with ht
  have ht0 : t ≠ 0 := by
    rw [ht]
    exact Complex.ofReal_ne_zero.mpr (half_pos hr0).ne'
  have htr : ‖t‖ = r / 2 := by
    rw [ht, Complex.norm_real, Real.norm_of_nonneg (half_pos hr0).le]
  have htm : t ∈ ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, htr]
    linarith
  have hζtm : ζ * t ∈ ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul, htr]
    linarith
  obtain ⟨z₁, hz₁S, hk1⟩ := hrsub htm
  obtain ⟨z₂, hz₂S, hk2⟩ := hrsub hζtm
  have hz12 : z₁ ≠ z₂ := by
    intro hcon
    rw [hcon] at hk1
    rw [hk1] at hk2
    have h3 : (ζ - 1) * t = 0 := by linear_combination -hk2
    rcases mul_eq_zero.mp h3 with h | h
    · exact hζ1 (sub_eq_zero.mp h)
    · exact ht0 h
  have hg1 : f z₁ - f a = k z₁ ^ n := hz₁S.2
  have hg2 : f z₂ - f a = k z₂ ^ n := hz₂S.2
  rw [hk1] at hg1
  rw [hk2] at hg2
  have hpow : (ζ * t) ^ n = t ^ n := by rw [mul_pow, hζn, one_mul]
  have hfeq : f z₁ = f z₂ := by linear_combination hg1 - hg2 - hpow
  exact hz12 (hinj hz₁S.1 hz₂S.1 hfeq)

/-- The local inverse of a holomorphic injection is continuous. -/
private lemma rmap_invFunOn_continuousAt {U : Set ℂ} (hUo : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {z : ℂ} (hz : z ∈ U) :
    ContinuousAt (Function.invFunOn f U) (f z) := by
  have hlinv : ∀ z' ∈ U, Function.invFunOn f U (f z') = z' :=
    fun z' hz' => Set.InjOn.leftInvOn_invFunOn hinj hz'
  have hfinv : Function.invFunOn f U (f z) = z := hlinv z hz
  have hder : deriv f z ≠ 0 := rmap_deriv_ne_zero_of_injOn hUo hf hinj hz
  have hstrict : HasStrictDerivAt f (deriv f z) z :=
    (hf.analyticAt (hUo.mem_nhds hz)).hasStrictDerivAt
  have hmeq : map f (𝓝 z) = 𝓝 (f z) := hstrict.map_nhds_eq hder
  unfold ContinuousAt
  rw [hfinv, tendsto_def]
  intro N hN
  have hmem : f '' (N ∩ U) ∈ 𝓝 (f z) := by
    rw [← hmeq]
    exact Filter.image_mem_map (Filter.inter_mem hN (hUo.mem_nhds hz))
  refine Filter.mem_of_superset hmem ?_
  rintro y ⟨z', ⟨hz'N, hz'U⟩, rfl⟩
  rw [Set.mem_preimage, hlinv z' hz'U]
  exact hz'N

/-- The inverse of a holomorphic bijection onto the disc lands back in `U`. -/
private lemma rmap_invFunOn_mem {U : Set ℂ} {f : ℂ → ℂ}
    (hbij : Set.BijOn f U (ball 0 1)) {w : ℂ} (hw : w ∈ ball 0 1) :
    Function.invFunOn f U w ∈ U ∧ f (Function.invFunOn f U w) = w := by
  obtain ⟨z, hzU, hzw⟩ := hbij.surjOn hw
  exact ⟨Function.invFunOn_mem ⟨z, hzU, hzw⟩,
    Function.invFunOn_eq ⟨z, hzU, hzw⟩⟩

/-- The inverse undoes `f` on `U`. -/
private lemma rmap_invFunOn_eq {U : Set ℂ} {f : ℂ → ℂ}
    (hinj : Set.InjOn f U) {z : ℂ} (hz : z ∈ U) :
    Function.invFunOn f U (f z) = z :=
  Set.InjOn.leftInvOn_invFunOn hinj hz

/-- The inverse of a holomorphic bijection onto the disc is holomorphic. -/
private lemma rmap_invFunOn_hasDerivAt {U : Set ℂ} (hUo : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hbij : Set.BijOn f U (ball 0 1)) {w : ℂ} (hw : w ∈ ball 0 1) :
    HasDerivAt (Function.invFunOn f U) (deriv f (Function.invFunOn f U w))⁻¹ w := by
  have hpre : ∀ y ∈ ball (0 : ℂ) 1,
      Function.invFunOn f U y ∈ U ∧ f (Function.invFunOn f U y) = y :=
    fun y hy => rmap_invFunOn_mem hbij hy
  have hwU : Function.invFunOn f U w ∈ U := (hpre w hw).1
  have hfw : f (Function.invFunOn f U w) = w := (hpre w hw).2
  have hfd : HasDerivAt f (deriv f (Function.invFunOn f U w))
      (Function.invFunOn f U w) :=
    (hf.differentiableAt (hUo.mem_nhds hwU)).hasDerivAt
  have hne : deriv f (Function.invFunOn f U w) ≠ 0 :=
    rmap_deriv_ne_zero_of_injOn hUo hf hbij.injOn hwU
  have hcont0 : ContinuousAt (Function.invFunOn f U)
      (f (Function.invFunOn f U w)) :=
    rmap_invFunOn_continuousAt hUo hf hbij.injOn hwU
  rw [hfw] at hcont0
  have hloc : ∀ᶠ y in 𝓝 w, f (Function.invFunOn f U y) = y := by
    have hball : ball (0 : ℂ) 1 ∈ 𝓝 w := Metric.isOpen_ball.mem_nhds hw
    filter_upwards [hball] with y hy
    exact (hpre y hy).2
  exact HasDerivAt.of_local_left_inverse hcont0 hfd hne hloc

/-- The inverse of a holomorphic bijection onto the disc is differentiable on it. -/
private lemma rmap_invFunOn_diffOn {U : Set ℂ} (hUo : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hbij : Set.BijOn f U (ball 0 1)) :
    DifferentiableOn ℂ (Function.invFunOn f U) (ball 0 1) := by
  intro w hw
  exact (rmap_invFunOn_hasDerivAt hUo hf hbij hw).differentiableAt.differentiableWithinAt

/-- Uniform derivative bound on the extremal family from Schwarz's lemma. -/
private lemma rmap_fam_deriv_bound {U : Set ℂ} (hUo : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball z₀ ρ ⊆ U ∧
      ∀ f ∈ rmap_Fam U z₀, ‖deriv f z₀‖ ≤ 1 / ρ := by
  obtain ⟨ρ, hr0, hrsub⟩ := Metric.isOpen_iff.mp hUo z₀ hz₀
  refine ⟨ρ, hr0, hrsub, fun f hf => ?_⟩
  obtain ⟨hfd, -, hmaps, hfz0⟩ := hf
  have hdiff : DifferentiableOn ℂ f (ball z₀ ρ) := hfd.mono hrsub
  have hmaps2 : Set.MapsTo f (ball z₀ ρ) (Metric.closedBall (f z₀) 1) := by
    have hsub : ball (0 : ℂ) 1 ⊆ Metric.closedBall (f z₀) 1 := by
      rw [hfz0]
      exact Metric.ball_subset_closedBall
    exact fun z hz => hsub (hmaps (hrsub hz))
  exact Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps2 hr0

/-- Facts about the supremum of derivatives on the extremal family. -/
private lemma rmap_sup_facts {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    BddAbove ((fun f => ‖deriv f z₀‖) '' rmap_Fam U z₀) ∧
      0 < sSup ((fun f => ‖deriv f z₀‖) '' rmap_Fam U z₀) ∧
      (∀ f ∈ rmap_Fam U z₀,
        ‖deriv f z₀‖ ≤ sSup ((fun f => ‖deriv f z₀‖) '' rmap_Fam U z₀)) ∧
      ∃ F : ℕ → ℂ → ℂ, (∀ n, F n ∈ rmap_Fam U z₀) ∧
        Tendsto (fun n => ‖deriv (F n) z₀‖) atTop
          (𝓝 (sSup ((fun f => ‖deriv f z₀‖) '' rmap_Fam U z₀))) := by
  set S : Set ℝ := (fun f => ‖deriv f z₀‖) '' rmap_Fam U z₀ with hSdef
  set M : ℝ := sSup S with hMdef
  obtain ⟨ρ, hr0, -, hbound⟩ := rmap_fam_deriv_bound hUo hz₀
  obtain ⟨f₀, hf₀⟩ := rmap_fam_nonempty hUo hUc hU hz₀
  have hfam : (rmap_Fam U z₀).Nonempty := ⟨f₀, hf₀⟩
  have hne : S.Nonempty := by
    rw [hSdef]
    exact hfam.image _
  have hbdd : BddAbove S := by
    refine ⟨1 / ρ, fun x hx => ?_⟩
    obtain ⟨f, hf, rfl⟩ := hx
    exact hbound f hf
  have hle : ∀ f ∈ rmap_Fam U z₀, ‖deriv f z₀‖ ≤ M := by
    intro f hf
    apply le_csSup hbdd
    rw [hSdef]
    exact ⟨f, hf, rfl⟩
  have hpos : 0 < M := by
    have h0 : deriv f₀ z₀ ≠ 0 :=
      rmap_deriv_ne_zero_of_injOn hUo hf₀.1 hf₀.2.1 hz₀
    have h1 : 0 < ‖deriv f₀ z₀‖ := norm_pos_iff.mpr h0
    have h2 : ‖deriv f₀ z₀‖ ≤ M := hle f₀ hf₀
    linarith
  have hseq : ∃ F : ℕ → ℂ → ℂ, (∀ n, F n ∈ rmap_Fam U z₀) ∧
      Tendsto (fun n => ‖deriv (F n) z₀‖) atTop (𝓝 M) := by
    have hN : ∀ n : ℕ, ∃ f ∈ rmap_Fam U z₀,
        M - 1 / ((n : ℝ) + 1) < ‖deriv f z₀‖ := by
      intro n
      have hlt : M - 1 / ((n : ℝ) + 1) < M := by
        have hpos1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨y, hyS, hltY⟩ := exists_lt_of_lt_csSup hne hlt
      obtain ⟨f, hfFam, rfl⟩ := hyS
      exact ⟨f, hfFam, hltY⟩
    choose F hF using hN
    refine ⟨F, fun n => (hF n).1, ?_⟩
    have e : Tendsto (fun _ : ℕ => M) atTop (𝓝 M) := tendsto_const_nhds
    have hg : Tendsto (fun n : ℕ => M - 1 / ((n : ℝ) + 1)) atTop (𝓝 M) := by
      have h := e.sub tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [show M - (0 : ℝ) = M from sub_zero M] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds
      (fun n => le_of_lt (hF n).2) (fun n => hle (F n) ((hF n).1))
  exact ⟨hbdd, hpos, hle, hseq⟩

/-- Extract a convergent subsequence from a maximizing sequence via Montel. -/
private lemma rmap_extract_limit {U : Set ℂ} (hUo : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {M : ℝ} {F : ℕ → ℂ → ℂ}
    (hFam : ∀ n, F n ∈ rmap_Fam U z₀)
    (hlim : Tendsto (fun n => ‖deriv (F n) z₀‖) atTop (𝓝 M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop U ∧
      f z₀ = 0 ∧ ‖deriv f z₀‖ = M ∧ ∀ z ∈ U, ‖f z‖ ≤ 1 := by
  have hB : MathlibExt.Analysis.Complex.NormalFamilies.IsLocallyUniformlyBoundedOn
      U F :=
    MathlibExt.Analysis.Complex.NormalFamilies.isLocallyUniformlyBoundedOn_of_forall_norm_le
      hUo zero_le_one (fun n y hy => by
        have h := (hFam n).2.2.1 hy
        have hlt : ‖F n y‖ < 1 := by
          simpa [Metric.mem_ball, dist_zero_right] using h
        exact hlt.le)
  obtain ⟨φ, hφ, f, hfdiff, hflu⟩ :=
    MathlibExt.Analysis.Complex.NormalFamilies.montel hUo F
      (fun n => (hFam n).1) hB
  have hfz0 : f z₀ = 0 := by
    have h1 : Tendsto (fun n => F (φ n) z₀) atTop (𝓝 (f z₀)) :=
      hflu.tendsto_at hz₀
    have h2 : Tendsto (fun n => F (φ n) z₀) atTop (𝓝 0) :=
      tendsto_const_nhds.congr (fun n => ((hFam (φ n)).2.2.2).symm)
    exact tendsto_nhds_unique h1 h2
  have hble : ∀ z ∈ U, ‖f z‖ ≤ 1 := by
    intro z hz
    have h1 : Tendsto (fun n => F (φ n) z) atTop (𝓝 (f z)) :=
      hflu.tendsto_at hz
    have hmem : f z ∈ Metric.closedBall (0 : ℂ) 1 := by
      apply IsClosed.mem_of_tendsto isClosed_closedBall h1
      filter_upwards with n
      have h := (hFam (φ n)).2.2.1 hz
      have hlt : ‖F (φ n) z‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using h
      simpa [Metric.mem_closedBall, dist_zero_right] using hlt.le
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  have hderiv : ‖deriv f z₀‖ = M := by
    have hder_lim := hflu.deriv
      (Filter.Eventually.of_forall fun n => (hFam (φ n)).1) hUo
    have h1 : Tendsto (fun n => deriv (F (φ n)) z₀) atTop (𝓝 (deriv f z₀)) :=
      hder_lim.tendsto_at hz₀
    have h1n : Tendsto (fun n => ‖deriv (F (φ n)) z₀‖) atTop (𝓝 ‖deriv f z₀‖) :=
      h1.norm
    have h2 : Tendsto (fun n => ‖deriv (F (φ n)) z₀‖) atTop (𝓝 M) :=
      hlim.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h1n h2
  exact ⟨φ, hφ, f, hfdiff, hflu, hfz0, hderiv, hble⟩

/-- A holomorphic function with nonzero derivative is nowhere locally constant. -/
private lemma rmap_not_eventually_const {U : Set ℂ} (hUo : IsOpen U)
    (hUpre : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hder : deriv f z₀ ≠ 0) :
    ∀ b ∈ U, ∀ c : ℂ, ¬ (f =ᶠ[𝓝 b] fun _ => c) := by
  intro b hb c hev
  have han : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hUo
  have heq : Set.EqOn f (fun _ => c) U :=
    han.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_const (v := c))
      hUpre hb hev
  have hev0 : f =ᶠ[𝓝 z₀] fun _ => c := by
    filter_upwards [hUo.mem_nhds hz₀] with z hz
    exact heq hz
  have hder0 : deriv f z₀ = deriv (fun _ => c) z₀ := hev0.deriv_eq
  rw [deriv_const] at hder0
  exact hder hder0

/-- The limit maps into the open disc by the maximum principle. -/
private lemma rmap_limit_mapsTo {U : Set ℂ} (hUo : IsOpen U)
    (hUpre : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hder : deriv f z₀ ≠ 0)
    (hble : ∀ z ∈ U, ‖f z‖ ≤ 1) : Set.MapsTo f U (ball 0 1) := by
  intro z₁ hz₁
  by_cases hlt : ‖f z₁‖ < 1
  · simpa [Metric.mem_ball, dist_zero_right] using hlt
  · have heq : ‖f z₁‖ = 1 := le_antisymm (hble z₁ hz₁) (not_lt.mp hlt)
    have hmax : IsMaxOn (norm ∘ f) U z₁ := by
      intro z hz
      simpa [heq] using hble z hz
    have heqOn :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUpre hUo hf hz₁ hmax
    have hev0 : f =ᶠ[𝓝 z₀] fun _ => f z₁ := by
      filter_upwards [hUo.mem_nhds hz₀] with z hz
      have hze := heqOn hz
      simpa using hze
    exact False.elim
      ((rmap_not_eventually_const hUo hUpre hz₀ hf hder z₀ hz₀ (f z₁)) hev0)

/-- The limit of injective maps is injective, by Hurwitz on a small ball. -/
private lemma rmap_limit_injOn {U : Set ℂ} (hUo : IsOpen U)
    (hUpre : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    {F : ℕ → ℂ → ℂ} (hFdiff : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFinj : ∀ n, Set.InjOn (F n) U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hder : deriv f z₀ ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) : Set.InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  obtain ⟨δ, hδ0, hδsub⟩ := Metric.isOpen_iff.mp hUo b hb
  have habd : 0 < dist a b := dist_pos.mpr hne
  set ε : ℝ := min δ (dist a b / 2) with hεdef
  have hε0 : 0 < ε := lt_min hδ0 (by linarith)
  have hεsub : ball b ε ⊆ U :=
    Subset.trans (Metric.ball_subset_ball (min_le_left _ _)) hδsub
  have haV : a ∉ ball b ε := by
    intro hmem
    rw [Metric.mem_ball] at hmem
    have hle : ε ≤ dist a b / 2 := min_le_right _ _
    linarith
  set V : Set ℂ := ball b ε with hVdef
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hVpre : IsPreconnected V := (convex_ball b ε).isPreconnected
  have hVsub : V ⊆ U := hεsub
  have hbV : b ∈ V := by
    rw [hVdef, Metric.mem_ball, dist_self]
    exact hε0
  have hFa : Tendsto (fun n => F n a) atTop (𝓝 (f a)) := hlim.tendsto_at ha
  have hconv : TendstoLocallyUniformlyOn (fun n z => F n z - F n a)
      (fun z => f z - f a) atTop V :=
    (hlim.mono hVsub).sub ((hFa.tendstoUniformlyOn_const V).tendstoLocallyUniformlyOn)
  have hFdiffV : ∀ n, DifferentiableOn ℂ (fun z => F n z - F n a) V := by
    intro n
    exact ((hFdiff n).sub_const (F n a)).mono hVsub
  have hGne : ∀ n, ∀ z ∈ V, F n z - F n a ≠ 0 := by
    intro n z hz h0
    have hza : z ≠ a := by
      intro h
      subst h
      exact haV hz
    have hfeq : F n z = F n a := sub_eq_zero.mp h0
    exact hza (hFinj n (hVsub hz) ha hfeq)
  have hex : ∃ z ∈ V, f z ≠ f a := by
    by_contra hall
    push Not at hall
    have hev : f =ᶠ[𝓝 b] fun _ => f a := by
      filter_upwards [hVopen.mem_nhds hbV] with z hz
      exact hall z hz
    exact rmap_not_eventually_const hUo hUpre hz₀ hf hder b hb (f a) hev
  obtain ⟨z, hzV, hzne⟩ := hex
  have hgne : (fun z => f z - f a) z ≠ 0 := sub_ne_zero.mpr hzne
  have hHur := TendstoLocallyUniformlyOn.ne_zero_of_exists_ne_zero
    hconv (Filter.Eventually.of_forall fun n => hFdiffV n)
    hVopen hVpre
    (Filter.Eventually.of_forall fun n z hz => hGne n z hz)
    ⟨z, hzV, hgne⟩
  have hbb : (fun z => f z - f a) b ≠ 0 := hHur b hbV
  have hcontra : f b - f a = 0 := by linear_combination -hab
  exact hbb hcontra

/-- There is a maximizing member of the extremal family. -/
private lemma rmap_exists_maximizer {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ f ∈ rmap_Fam U z₀, deriv f z₀ ≠ 0 ∧
      ∀ g ∈ rmap_Fam U z₀, ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  obtain ⟨hbdd, hpos, hle, F, hFam, hFlim⟩ := rmap_sup_facts hUo hUc hU hz₀
  set M : ℝ := sSup ((fun f => ‖deriv f z₀‖) '' rmap_Fam U z₀) with hMdef
  obtain ⟨φ, hφ, f, hfdiff, hflu, hfz0, hderivM, hble⟩ :=
    rmap_extract_limit hUo hz₀ hFam hFlim
  have hder0 : deriv f z₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hderivM
    linarith
  have hpre := rmap_isPreconnected hUc
  have hmaps : Set.MapsTo f U (ball 0 1) :=
    rmap_limit_mapsTo hUo hpre hz₀ hfdiff hder0 hble
  have hinj : Set.InjOn f U :=
    rmap_limit_injOn hUo hpre hz₀ (fun n => (hFam (φ n)).1)
      (fun n => (hFam (φ n)).2.1) hfdiff hder0 hflu
  refine ⟨f, ⟨hfdiff, hinj, hmaps, hfz0⟩, hder0, fun g hg => ?_⟩
  rw [hderivM]
  exact hle g hg

/-- The square-root-trick map `ψ` at `0` equals `0`. -/
private lemma rmap_psi_zero {b : ℂ} :
    (fun w => rmap_mob (b ^ 2) ((rmap_mob (-b) w) ^ 2)) 0 = 0 := by
  have hbeta : (fun w => rmap_mob (b ^ 2) ((rmap_mob (-b) w) ^ 2)) 0
      = rmap_mob (b ^ 2) ((rmap_mob (-b) 0) ^ 2) := rfl
  rw [hbeta, rmap_mob_zero, neg_neg, rmap_mob_self]

/-- The derivative of the square-root-trick map at `0`. -/
private lemma rmap_psi_hasDerivAt {b : ℂ} (hb : ‖b‖ < 1) :
    HasDerivAt (fun w => rmap_mob (b ^ 2) ((rmap_mob (-b) w) ^ 2))
      (2 * b / (1 + ((‖b‖ ^ 2 : ℝ) : ℂ))) 0 := by
  have hb2 : ‖b ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hb (by norm_num)
  have hnb : ‖-b‖ < 1 := by rwa [norm_neg]
  have hval : rmap_mob (-b) 0 = b := by rw [rmap_mob_zero, neg_neg]
  have hval2 : (fun w => (rmap_mob (-b) w) ^ 2) 0 = b ^ 2 := by
    have hbeta : (fun w => (rmap_mob (-b) w) ^ 2) 0
        = (rmap_mob (-b) 0) ^ 2 := rfl
    rw [hbeta, hval]
  have eR : starRingEnd ℂ b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, Complex.ofReal_pow]
    exact Complex.conj_mul' b
  have eT : starRingEnd ℂ (b ^ 2) * (b ^ 2) = (((‖b‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
    rw [map_pow]
    have hsq : (starRingEnd ℂ b) ^ 2 * b ^ 2 = (starRingEnd ℂ b * b) ^ 2 := by
      ring
    rw [hsq, eR, Complex.ofReal_pow]
  have hden0 : (1 : ℂ) - starRingEnd ℂ (-b) * 0 ≠ 0 := by simp
  have h1 : HasDerivAt (rmap_mob (-b)) (1 - starRingEnd ℂ b * b) 0 := by
    have h := rmap_mob_hasDerivAt (-b) 0 hden0
    refine h.congr_deriv ?_
    simp only [map_neg, mul_zero, sub_zero, one_pow, div_one, neg_mul_neg]
  have h2 : HasDerivAt (fun w => (rmap_mob (-b) w) ^ 2)
      (2 * b * (1 - starRingEnd ℂ b * b)) 0 := by
    have hh : HasDerivAt (fun u : ℂ => u ^ 2) (2 * b) b := by
      have h := hasDerivAt_pow 2 b
      simpa using h
    have h := HasDerivAt.comp_of_eq 0 hh h1 hval.symm
    refine h.congr_deriv ?_
    ring
  have hden2 : (1 : ℂ) - starRingEnd ℂ (b ^ 2) * (b ^ 2) ≠ 0 :=
    rmap_mob_den hb2 hb2
  have houter : HasDerivAt (rmap_mob (b ^ 2))
      ((1 - starRingEnd ℂ (b ^ 2) * (b ^ 2)) /
        (1 - starRingEnd ℂ (b ^ 2) * (b ^ 2)) ^ 2) (b ^ 2) :=
    rmap_mob_hasDerivAt _ _ hden2
  have houter' : HasDerivAt (rmap_mob (b ^ 2))
      ((1 - starRingEnd ℂ (b ^ 2) * (b ^ 2)) /
        (1 - starRingEnd ℂ (b ^ 2) * (b ^ 2)) ^ 2)
      ((fun w => (rmap_mob (-b) w) ^ 2) 0) := by
    rw [hval2]
    exact houter
  have htot := HasDerivAt.comp 0 houter' h2
  have hr_lt : ‖b‖ ^ 2 < 1 := (sq_lt_one_iff₀ (norm_nonneg _)).mpr hb
  have hu1 : (1 : ℂ) - ((‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hfac : (1 : ℂ) - ((‖b‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖b‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hfac]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hu2 : (1 : ℂ) + ((‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hfac : (1 : ℂ) + ((‖b‖ ^ 2 : ℝ) : ℂ) = ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hfac]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hu12 : (1 : ℂ) - ((‖b‖ ^ 2 : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have hfac : (1 : ℂ) - ((‖b‖ ^ 2 : ℝ) : ℂ) ^ 2 =
        (1 - ((‖b‖ ^ 2 : ℝ) : ℂ)) * (1 + ((‖b‖ ^ 2 : ℝ) : ℂ)) := by
      ring
    rw [hfac]
    exact mul_ne_zero hu1 hu2
  refine htot.congr_deriv ?_
  rw [eR, eT]
  field_simp
  ring

/-- The norm of the derivative of the square-root-trick map at `0` is `< 1`. -/
private lemma rmap_psi_deriv_norm {b : ℂ} (hb : ‖b‖ < 1) :
    ‖2 * b / (1 + ((‖b‖ ^ 2 : ℝ) : ℂ))‖ < 1 := by
  have hpos : (0 : ℝ) < 1 + ‖b‖ ^ 2 := by positivity
  have hnorm : ‖(1 : ℂ) + ((‖b‖ ^ 2 : ℝ) : ℂ)‖ = 1 + ‖b‖ ^ 2 := by
    have hfac : (1 : ℂ) + ((‖b‖ ^ 2 : ℝ) : ℂ) = ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hfac, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  rw [Complex.norm_div, Complex.norm_mul, hnorm, div_lt_one hpos]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hne : (1 : ℝ) - ‖b‖ ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt hb
  have hsq : (0 : ℝ) < (1 - ‖b‖) ^ 2 := sq_pos_of_ne_zero hne
  nlinarith

/-- The square-root trick: a family member missing `c` factors through `ψ`. -/
private lemma rmap_sqrt_trick {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f : ℂ → ℂ}
    (hf : f ∈ rmap_Fam U z₀) {c : ℂ} (hc : ‖c‖ < 1)
    (hmiss : ∀ z ∈ U, f z ≠ c) :
    ∃ b : ℂ, ‖b‖ < 1 ∧ ∃ F : ℂ → ℂ, F ∈ rmap_Fam U z₀ ∧
      ∀ z ∈ U, f z
        = (fun w => rmap_mob (b ^ 2) ((rmap_mob (-b) w) ^ 2)) (F z) := by
  obtain ⟨hfdiff, hfinj, hmaps, hfz0⟩ := hf
  have hfnorm : ∀ z ∈ U, ‖f z‖ < 1 := by
    intro z hz
    have h := hmaps hz
    simpa [Metric.mem_ball, dist_zero_right] using h
  have hGdiff : DifferentiableOn ℂ (fun z => rmap_mob c (f z)) U :=
    (rmap_mob_diffOn hc).comp hfdiff hmaps
  have hGlt : ∀ z ∈ U, ‖rmap_mob c (f z)‖ < 1 := by
    intro z hz
    exact rmap_mob_maps hc (hfnorm z hz)
  have hG0 : ∀ z ∈ U, rmap_mob c (f z) ≠ 0 := by
    intro z hz hcon
    have hmem : f z ∈ ball (0 : ℂ) 1 := hmaps hz
    have hnorm : ‖f z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hmem
    have heq := (rmap_mob_eq_zero hc hnorm).mp hcon
    exact hmiss z hz heq
  obtain ⟨s, hsdiff, hsq⟩ := rmap_exists_holo_sqrt hUo hUc hGdiff hG0
  have hsnorm : ∀ z ∈ U, ‖s z‖ < 1 := by
    intro z hz
    have h1 : ‖s z‖ ^ 2 < 1 := by
      have h2 : ‖s z ^ 2‖ < 1 := by
        rw [hsq z hz]
        exact hGlt z hz
      rwa [norm_pow] at h2
    exact (sq_lt_one_iff₀ (norm_nonneg _)).mp h1
  have hsmem : ∀ z ∈ U, s z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    simpa [Metric.mem_ball, dist_zero_right] using hsnorm z hz
  have hsinj : Set.InjOn s U := by
    intro z hz w hw hzw
    have hzw' : s z ^ 2 = s w ^ 2 := congrArg (· ^ 2) hzw
    rw [hsq z hz, hsq w hw] at hzw'
    have hmob : rmap_mob (-c) (rmap_mob c (f z))
        = rmap_mob (-c) (rmap_mob c (f w)) := congrArg _ hzw'
    rw [rmap_mob_inv hc (hfnorm z hz), rmap_mob_inv hc (hfnorm w hw)] at hmob
    exact hfinj hz hw hmob
  refine ⟨s z₀, hsnorm z₀ hz₀, fun z => rmap_mob (s z₀) (s z), ?_, ?_⟩
  · have hFdiff : DifferentiableOn ℂ (fun z => rmap_mob (s z₀) (s z)) U :=
      (rmap_mob_diffOn (hsnorm z₀ hz₀)).comp hsdiff
        (fun z hz => hsmem z hz)
    have hFmaps : Set.MapsTo (fun z => rmap_mob (s z₀) (s z)) U (ball 0 1) := by
      intro z hz
      simpa [Metric.mem_ball, dist_zero_right] using
        rmap_mob_maps (hsnorm z₀ hz₀) (hsnorm z hz)
    have hFinj : Set.InjOn (fun z => rmap_mob (s z₀) (s z)) U := by
      intro z hz w hw heq
      have heq' : rmap_mob (s z₀) (s z) = rmap_mob (s z₀) (s w) := heq
      have hmob : rmap_mob (-(s z₀)) (rmap_mob (s z₀) (s z))
          = rmap_mob (-(s z₀)) (rmap_mob (s z₀) (s w)) := congrArg _ heq'
      rw [rmap_mob_inv (hsnorm z₀ hz₀) (hsnorm z hz),
        rmap_mob_inv (hsnorm z₀ hz₀) (hsnorm w hw)] at hmob
      exact hsinj hz hw hmob
    have hFz0 : (fun z => rmap_mob (s z₀) (s z)) z₀ = 0 := rmap_mob_self _
    exact ⟨hFdiff, hFinj, hFmaps, hFz0⟩
  · intro z hz
    have hbeta : (fun w => rmap_mob ((s z₀) ^ 2) ((rmap_mob (-(s z₀)) w) ^ 2))
        (rmap_mob (s z₀) (s z))
        = rmap_mob ((s z₀) ^ 2)
          ((rmap_mob (-(s z₀)) (rmap_mob (s z₀) (s z))) ^ 2) := rfl
    rw [hbeta, rmap_mob_inv (hsnorm z₀ hz₀) (hsnorm z hz), hsq z hz]
    have hb2 : (s z₀) ^ 2 = -c := by
      have h1 := hsq z₀ hz₀
      rw [hfz0, rmap_mob_zero] at h1
      exact h1
    rw [hb2]
    exact (rmap_mob_inv hc (hfnorm z hz)).symm

/-- The maximizer is onto the disc, hence a bijection. -/
private lemma rmap_maximizer_surjOn {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f : ℂ → ℂ}
    (hf : f ∈ rmap_Fam U z₀) (hder : deriv f z₀ ≠ 0)
    (hmax : ∀ g ∈ rmap_Fam U z₀, ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    Set.BijOn f U (ball 0 1) := by
  obtain ⟨hfdiff, hfinj, hmaps, hfz0⟩ := hf
  have hsurj : Set.SurjOn f U (ball 0 1) := by
    intro c hc
    have hcnorm : ‖c‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hc
    by_contra hcon
    have hmiss : ∀ z ∈ U, f z ≠ c := by
      intro z hz hcc
      exact hcon ⟨z, hz, hcc⟩
    obtain ⟨b, hb, F, hF, hFeq⟩ :=
      rmap_sqrt_trick hUo hUc hz₀ ⟨hfdiff, hfinj, hmaps, hfz0⟩ hcnorm hmiss
    have hFdiff : DifferentiableOn ℂ F U := hF.1
    have hFz0 : F z₀ = 0 := hF.2.2.2
    have hev : f =ᶠ[𝓝 z₀]
        (fun z => (fun w => rmap_mob (b ^ 2) ((rmap_mob (-b) w) ^ 2)) (F z)) := by
      filter_upwards [hUo.mem_nhds hz₀] with z hz
      exact hFeq z hz
    have hFder : HasDerivAt F (deriv F z₀) z₀ :=
      (hFdiff.differentiableAt (hUo.mem_nhds hz₀)).hasDerivAt
    have hcompLam : HasDerivAt
        (fun z => (fun w => rmap_mob (b ^ 2) ((rmap_mob (-b) w) ^ 2)) (F z))
        ((2 * b / (1 + ((‖b‖ ^ 2 : ℝ) : ℂ))) * deriv F z₀) z₀ :=
      HasDerivAt.comp_of_eq z₀ (rmap_psi_hasDerivAt hb) hFder hFz0.symm
    have hfder : HasDerivAt f
        ((2 * b / (1 + ((‖b‖ ^ 2 : ℝ) : ℂ))) * deriv F z₀) z₀ :=
      HasDerivAt.congr_of_eventuallyEq hcompLam hev
    have hder_eq : deriv f z₀
        = (2 * b / (1 + ((‖b‖ ^ 2 : ℝ) : ℂ))) * deriv F z₀ := hfder.deriv
    have hFne : deriv F z₀ ≠ 0 := by
      intro h0
      rw [hder_eq, h0, mul_zero] at hder
      exact hder rfl
    have hFpos : 0 < ‖deriv F z₀‖ := norm_pos_iff.mpr hFne
    have hlt : ‖2 * b / (1 + ((‖b‖ ^ 2 : ℝ) : ℂ))‖ < 1 :=
      rmap_psi_deriv_norm hb
    have hcontra : ‖deriv f z₀‖ < ‖deriv F z₀‖ := by
      have hnorm : ‖deriv f z₀‖
          = ‖2 * b / (1 + ((‖b‖ ^ 2 : ℝ) : ℂ))‖ * ‖deriv F z₀‖ := by
        rw [hder_eq, Complex.norm_mul]
      rw [hnorm]
      exact mul_lt_of_lt_one_left hFpos hlt
    have hle := hmax F hF
    linarith
  exact Set.BijOn.mk hmaps hfinj hsurj

/-- Rotate a disc bijection so its derivative at `z₀` is a positive real. -/
private lemma rmap_rotate {U : Set ℂ} (hUo : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hbij : Set.BijOn f U (ball 0 1))
    (hfz0 : f z₀ = 0) (hd0 : deriv f z₀ ≠ 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ Set.BijOn F U (ball 0 1) ∧
      F z₀ = 0 ∧ deriv F z₀ = ((‖deriv f z₀‖ : ℝ) : ℂ) ∧
      (deriv F z₀).im = 0 ∧ 0 < (deriv F z₀).re := by
  set lam : ℂ := ((‖deriv f z₀‖ : ℝ) : ℂ) / deriv f z₀ with hlamdef
  have hnum : ‖((‖deriv f z₀‖ : ℝ) : ℂ)‖ = ‖deriv f z₀‖ := by
    rw [Complex.norm_real]
    exact norm_norm _
  have hlamnorm : ‖lam‖ = 1 := by
    rw [hlamdef, Complex.norm_div, hnum]
    exact div_self (norm_pos_iff.mpr hd0).ne'
  have hlam0 : lam ≠ 0 := by
    rw [hlamdef]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hd0).ne') hd0
  have hfnorm : ∀ z ∈ U, ‖f z‖ < 1 := by
    intro z hz
    have h := hbij.mapsTo hz
    simpa [Metric.mem_ball, dist_zero_right] using h
  have hFdiff : DifferentiableOn ℂ (fun z => lam * f z) U :=
    (differentiableOn_const lam).mul hf
  have hFmaps : Set.MapsTo (fun z => lam * f z) U (ball 0 1) := by
    intro z hz
    have h1 : ‖lam * f z‖ < 1 := by
      rw [Complex.norm_mul, hlamnorm, one_mul]
      exact hfnorm z hz
    simpa [Metric.mem_ball, dist_zero_right] using h1
  have hFinj : Set.InjOn (fun z => lam * f z) U := by
    intro z hz w hw heq
    have heq' : lam * f z = lam * f w := heq
    have hfw : f z = f w := mul_left_cancel₀ hlam0 heq'
    exact hbij.injOn hz hw hfw
  have hFsurj : Set.SurjOn (fun z => lam * f z) U (ball 0 1) := by
    intro w hw
    have hwnorm : ‖w‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hw
    have hinv : ‖lam⁻¹ * w‖ < 1 := by
      rw [norm_mul, norm_inv, hlamnorm, inv_one, one_mul]
      exact hwnorm
    have hmem : lam⁻¹ * w ∈ ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hinv
    obtain ⟨z, hzU, hzw⟩ := hbij.surjOn hmem
    refine ⟨z, hzU, ?_⟩
    have hbeta : (fun z => lam * f z) z = lam * f z := rfl
    rw [hbeta, hzw, ← mul_assoc, mul_inv_cancel₀ hlam0, one_mul]
  have hFz0 : (fun z => lam * f z) z₀ = 0 := by
    have hbeta : (fun z => lam * f z) z₀ = lam * f z₀ := rfl
    rw [hbeta, hfz0, mul_zero]
  have hFder : deriv (fun z => lam * f z) z₀ = ((‖deriv f z₀‖ : ℝ) : ℂ) := by
    have hder : HasDerivAt (fun z => lam * f z) (lam * deriv f z₀) z₀ :=
      HasDerivAt.const_mul lam ((hf.differentiableAt (hUo.mem_nhds hz₀)).hasDerivAt)
    have h := hder.deriv
    rw [hlamdef, div_mul_cancel₀ _ hd0] at h
    exact h
  refine ⟨fun z => lam * f z, hFdiff, Set.BijOn.mk hFmaps hFinj hFsurj, hFz0,
    hFder, ?_, ?_⟩
  · rw [hFder, Complex.ofReal_im]
  · rw [hFder, Complex.ofReal_re]
    exact norm_pos_iff.mpr hd0

/-- Schwarz comparison of two normalized disc bijections. -/
private lemma rmap_schwarz_le {U : Set ℂ} (hUo : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hfbij : Set.BijOn f U (ball 0 1))
    (hg : DifferentiableOn ℂ g U) (hgbij : Set.BijOn g U (ball 0 1))
    (hfz0 : f z₀ = 0) (hgz0 : g z₀ = 0) :
    DifferentiableOn ℂ (fun w => g (Function.invFunOn f U w)) (ball 0 1) ∧
    HasDerivAt (fun w => g (Function.invFunOn f U w))
      (deriv g z₀ * (deriv f z₀)⁻¹) 0 ∧
    ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  have hfinv_maps : Set.MapsTo (Function.invFunOn f U) (ball 0 1) U := by
    intro w hw
    exact (rmap_invFunOn_mem hfbij hw).1
  have hdiff : DifferentiableOn ℂ (fun w => g (Function.invFunOn f U w))
      (ball 0 1) :=
    hg.comp (rmap_invFunOn_diffOn hUo hf hfbij) hfinv_maps
  have hmaps : Set.MapsTo (fun w => g (Function.invFunOn f U w))
      (ball 0 1) (ball 0 1) := by
    intro w hw
    exact hgbij.mapsTo (hfinv_maps hw)
  have hfinv0 : Function.invFunOn f U 0 = z₀ := by
    rw [← hfz0]
    exact rmap_invFunOn_eq hfbij.injOn hz₀
  have hh0 : (fun w => g (Function.invFunOn f U w)) 0 = 0 := by
    have hbeta : (fun w => g (Function.invFunOn f U w)) 0
        = g (Function.invFunOn f U 0) := rfl
    rw [hbeta, hfinv0, hgz0]
  have hfinv_der : HasDerivAt (Function.invFunOn f U) (deriv f z₀)⁻¹ 0 := by
    have h := rmap_invFunOn_hasDerivAt hUo hf hfbij
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
    rwa [hfinv0] at h
  have hg_der : HasDerivAt g (deriv g z₀) z₀ :=
    (hg.differentiableAt (hUo.mem_nhds hz₀)).hasDerivAt
  have hcompLam : HasDerivAt (fun w => g (Function.invFunOn f U w))
      (deriv g z₀ * (deriv f z₀)⁻¹) 0 :=
    HasDerivAt.comp_of_eq 0 hg_der hfinv_der hfinv0.symm
  have hfne : deriv f z₀ ≠ 0 :=
    rmap_deriv_ne_zero_of_injOn hUo hf hfbij.injOn hz₀
  have hpos : 0 < ‖deriv f z₀‖ := norm_pos_iff.mpr hfne
  have hmaps_closed : Set.MapsTo (fun w => g (Function.invFunOn f U w))
      (ball 0 1)
      (Metric.closedBall ((fun w => g (Function.invFunOn f U w)) 0) 1) := by
    rw [hh0]
    exact fun w hw => Metric.ball_subset_closedBall (hmaps hw)
  have hbound := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps_closed
    (by norm_num : (0 : ℝ) < 1)
  have hder0 : deriv (fun w => g (Function.invFunOn f U w)) 0
      = deriv g z₀ * (deriv f z₀)⁻¹ := hcompLam.deriv
  have hle : ‖deriv g z₀‖ / ‖deriv f z₀‖ ≤ 1 := by
    rw [hder0, Complex.norm_mul, norm_inv] at hbound
    simpa [div_eq_mul_inv] using hbound
  refine ⟨hdiff, hcompLam, (div_le_one hpos).mp hle⟩

/-- Schwarz equality case: equal derivatives force equality on `U`. -/
private lemma rmap_schwarz_eqOn {U : Set ℂ} (hUo : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hfbij : Set.BijOn f U (ball 0 1))
    (hg : DifferentiableOn ℂ g U) (hgbij : Set.BijOn g U (ball 0 1))
    (hfz0 : f z₀ = 0) (hgz0 : g z₀ = 0)
    (hdeq : deriv g z₀ = deriv f z₀) :
    Set.EqOn g f U := by
  have hschw := rmap_schwarz_le hUo hz₀ hf hfbij hg hgbij hfz0 hgz0
  have hdiff := hschw.1
  have hcompLam := hschw.2.1
  have hfne : deriv f z₀ ≠ 0 :=
    rmap_deriv_ne_zero_of_injOn hUo hf hfbij.injOn hz₀
  have hdslope : dslope (fun w => g (Function.invFunOn f U w)) 0 0 = 1 := by
    rw [dslope_same, hcompLam.deriv, hdeq, mul_inv_cancel₀ hfne]
  have hnorm : ‖dslope (fun w => g (Function.invFunOn f U w)) 0 0‖
      = 1 / 1 := by
    rw [hdslope, norm_one, div_one]
  have hfinv0 : Function.invFunOn f U 0 = z₀ := by
    rw [← hfz0]
    exact rmap_invFunOn_eq hfbij.injOn hz₀
  have hh0 : (fun w => g (Function.invFunOn f U w)) 0 = 0 := by
    have hbeta : (fun w => g (Function.invFunOn f U w)) 0
        = g (Function.invFunOn f U 0) := rfl
    rw [hbeta, hfinv0, hgz0]
  have hmaps : Set.MapsTo (fun w => g (Function.invFunOn f U w))
      (ball 0 1) (ball 0 1) := by
    intro w hw
    exact hgbij.mapsTo ((rmap_invFunOn_mem hfbij hw).1)
  have hmaps_closed : Set.MapsTo (fun w => g (Function.invFunOn f U w))
      (ball 0 1)
      (Metric.closedBall ((fun w => g (Function.invFunOn f U w)) 0) 1) := by
    rw [hh0]
    exact fun w hw => Metric.ball_subset_closedBall (hmaps hw)
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hdiff
    hmaps_closed (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) hnorm
  intro z hz
  have hfzball : f z ∈ ball (0 : ℂ) 1 := hfbij.mapsTo hz
  have h1 : g (Function.invFunOn f U (f z))
      = (fun w => g (Function.invFunOn f U w)) 0
        + (f z - 0)
          • dslope (fun w => g (Function.invFunOn f U w)) 0 0 :=
    haff hfzball
  rw [rmap_invFunOn_eq hfbij.injOn hz, hh0, hdslope] at h1
  simpa using h1

/-- Positive-real complex numbers are determined by their norm. -/
private lemma rmap_posReal_eq {d e : ℂ} (hd_im : d.im = 0) (hd_re : 0 < d.re)
    (he_im : e.im = 0) (he_re : 0 < e.re) (hde : ‖d‖ = ‖e‖) : d = e := by
  have hd_eq : d.re = ‖d‖ := by
    have h : |d.re| = ‖d‖ := (Complex.abs_re_eq_norm).mpr hd_im
    rwa [abs_of_pos hd_re] at h
  have he_eq : e.re = ‖e‖ := by
    have h : |e.re| = ‖e‖ := (Complex.abs_re_eq_norm).mpr he_im
    rwa [abs_of_pos he_re] at h
  apply Complex.ext
  · rw [hd_eq, he_eq, hde]
  · rw [hd_im, he_im]

/--
For open simply connected proper `U ⊆ ℂ` and `z₀ ∈ U`, there exists holomorphic bijection `f : U →
ball 0 1` with `f z₀ = 0` and `deriv f z₀` positive real, unique up to `Set.EqOn` on `U`. Source:
same as Riemann mapping; B. Riemann thesis 1851; W. F. Osgood Trans. Amer. Math. Soc. 1 (1900),
310–314, DOI 10.2307/1986285; C. Carathéodory Math. Ann. 72 (1912), 107–144, DOI
10.1007/BF01456892; Ahlfors; Lean adds f z₀=0 positive real derivative via im=0 re>0 and EqOn
uniqueness on U.

Proves `Wanted` entry `riemannMapping_normalized`.
-/
public theorem riemannMapping_normalized
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ Set.BijOn f U (Metric.ball (0 : ℂ) 1) ∧
      f z₀ = 0 ∧ (deriv f z₀).im = 0 ∧ 0 < (deriv f z₀).re ∧
      ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → Set.BijOn g U (Metric.ball (0 : ℂ) 1) →
        g z₀ = 0 → (deriv g z₀).im = 0 → 0 < (deriv g z₀).re →
        Set.EqOn f g U := by
  obtain ⟨f, hfmem, hder0, hmax⟩ := rmap_exists_maximizer hUo hUc hU hz₀
  have hfdiff : DifferentiableOn ℂ f U := hfmem.1
  have hfz0 : f z₀ = 0 := hfmem.2.2.2
  have hbij := rmap_maximizer_surjOn hUo hUc hz₀ hfmem hder0 hmax
  obtain ⟨F, hFdiff, hFbij, hFz0, -, hFim, hFre⟩ :=
    rmap_rotate hUo hz₀ hfdiff hbij hfz0 hder0
  refine ⟨F, hFdiff, hFbij, hFz0, hFim, hFre,
    fun g hg hgbij hgz0 hgim hgre => ?_⟩
  have hle1 := (rmap_schwarz_le hUo hz₀ hFdiff hFbij hg hgbij hFz0 hgz0).2.2
  have hle2 := (rmap_schwarz_le hUo hz₀ hg hgbij hFdiff hFbij hgz0 hFz0).2.2
  have hnorm : ‖deriv g z₀‖ = ‖deriv F z₀‖ := le_antisymm hle1 hle2
  have hder_eq : deriv g z₀ = deriv F z₀ :=
    rmap_posReal_eq hgim hgre hFim hFre hnorm
  have heq := rmap_schwarz_eqOn hUo hz₀ hFdiff hFbij hg hgbij hFz0 hgz0 hder_eq
  exact heq.symm

end MathlibExt.Analysis.Complex.RiemannMappingWanted
