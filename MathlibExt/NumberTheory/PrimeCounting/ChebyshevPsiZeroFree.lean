/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Error terms in the prime number theorem bound the zeros of `ζ`

If `ψ(x) - x = O(x^{θ + ε})` for every `ε > 0`, then the Mellin transform of `ψ(x) - x` continues
`-ζ'/ζ(s) - s/(s - 1)` holomorphically to `Re s > θ`, so `ζ` has no zeros there. In particular
`ψ(x) = x + O(x^{1/2} log² x)` implies that `ζ(s) ≠ 0` for `Re s > 1/2`.

## Main statements

* `LSeries_vonMangoldt_eq_mul_integral_chebyshevPsi`:
  `∑ Λ(n) n^{-s} = s ∫_1^∞ ψ(t) t^{-s-1} dt` for `Re s > 1`.
* `riemannZeta_ne_zero_of_forall_isBigO_rpow`: if `ψ(x) - x = O(x^{θ + ε})` for all `ε > 0`,
  then `ζ(s) ≠ 0` for `Re s > θ`.
* `riemannZeta_ne_zero_of_psi_sub_self_isBigO`: if `ψ(x) - x = O(x^{1/2} log² x)`, then
  `ζ(s) ≠ 0` for `Re s > 1/2`.
-/

@[expose] public section

open Asymptotics Filter MeasureTheory

/-- **The Mellin representation of `-ζ'/ζ`.** For `Re s > 1`,
`∑ Λ(n) n^{-s} = s ∫_1^∞ ψ(t) t^{-s-1} dt`. -/
theorem LSeries_vonMangoldt_eq_mul_integral_chebyshevPsi {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      s * ∫ t in Set.Ioi (1 : ℝ), ((Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; linarith
  set F : ℕ → ℝ → ℂ := fun n => Set.indicator (Set.Ici (n : ℝ))
    (fun t => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) with hF
  have hval : ∀ n : ℕ, ∫ t, F n t =
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s) / s := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [hF]; dsimp only
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_Ioi_cpow_of_lt (by simp; linarith) hn', show -s - 1 + 1 = -s by ring,
      neg_div_neg_eq]
    push_cast
    ring
  have hint : ∀ n, Integrable (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    refine (integrable_indicator_iff measurableSet_Ici).mpr ?_
    have hI := integrableOn_Ioi_cpow_of_lt (a := -s - 1) (by simp; linarith)
      (Nat.cast_pos.mpr hn)
    exact ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hI).const_mul _
  have hnorm : ∀ n : ℕ, ∫ t, ‖F n t‖ =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) / s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have : (fun t => ‖F n t‖) = Set.indicator (Set.Ici (n : ℝ))
        (fun t => ArithmeticFunction.vonMangoldt n * t ^ (-s.re - 1)) := by
      ext t
      by_cases ht : (n : ℝ) ≤ t
      · have ht0 : 0 < t := lt_of_lt_of_le hn' ht
        simp only [F, Set.indicator_of_mem (Set.mem_Ici.mpr ht)]
        rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        simp
      · simp [F, Set.indicator_of_notMem, Set.mem_Ici, ht]
    rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hn',
      show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]
    ring
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hnorm]
    refine ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm.div_const s.re).congr
      (fun n => ?_)
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [ite_eq_right hn.ne', Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have hpt : ∀ t : ℝ, ∑' n, F n t = ((Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    intro t
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊t⌋₊)]
    · rw [Chebyshev.psi]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hn' := Finset.mem_Ioc.mp hn
      have ht : (n : ℝ) ≤ t := by
        have h1 : 1 ≤ ⌊t⌋₊ := lt_of_lt_of_le hn'.1 hn'.2
        have h0 : 0 ≤ t := by
          by_contra hneg
          rw [Nat.floor_eq_zero.mpr (by linarith)] at h1
          omega
        exact (Nat.le_floor_iff h0).mp hn'.2
      simp [F, Set.indicator_of_mem (Set.mem_Ici.mpr ht)]
    · intro n hn
      rw [Finset.mem_Ioc, not_and_or] at hn
      rcases hn with hn | hn
      · have : n = 0 := by omega
        subst this; simp [F]
      · have ht : ¬ (n : ℝ) ≤ t := by
          intro h
          rcases lt_or_ge t 0 with h0 | h0
          · have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
            have : n = 0 := by exact_mod_cast le_antisymm (by linarith) this
            omega
          · exact hn ((Nat.le_floor_iff h0).mpr h)
        simp [F, Set.indicator_of_notMem, Set.mem_Ici, ht]
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hpt, hval] at key
  have hsupp : ∫ t, ((Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
      ∫ t in Set.Ioi (1 : ℝ), ((Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    ext t
    by_cases ht : 1 < t
    · simp [Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
    · simp [Set.indicator_of_notMem, Set.mem_Ioi, ht,
        Chebyshev.psi_eq_zero_of_le_one (not_lt.mp ht)]
  rw [← hsupp, ← key, tsum_div_const, mul_div_cancel₀ _ hs0, LSeries]
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ite_eq_right hn.ne', Complex.cpow_neg, div_eq_mul_inv]

/-- The error term `ψ(t) - t`, cut off to `t > 1`, as a complex-valued function. -/
private noncomputable def psiErr : ℝ → ℂ :=
  Set.indicator (Set.Ioi (1 : ℝ)) (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ))

private lemma psiErr_locallyIntegrableOn : LocallyIntegrableOn psiErr (Set.Ioi 0) := by
  have h1 : LocallyIntegrable (fun t : ℝ => Chebyshev.psi t - t) volume :=
    Chebyshev.psi_mono.locallyIntegrable.sub continuous_id.locallyIntegrable
  have h2 : LocallyIntegrable (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ)) volume := by
    have := Complex.ofRealCLM.locallyIntegrableOn_comp (h1.locallyIntegrableOn Set.univ)
    rwa [locallyIntegrableOn_univ] at this
  exact (h2.indicator measurableSet_Ioi).locallyIntegrableOn _

private lemma psiErr_isBigO {θ : ℝ}
    (h : ∀ ε > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (θ + ε)))
    {a : ℝ} (ha : a < -θ) :
    psiErr =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  have hf : psiErr =ᶠ[atTop] (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ)) := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [psiErr, Set.indicator_of_mem, ht]
  have hc : (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Chebyshev.psi t - t) :=
    isBigO_of_le _ (fun t => by rw [Complex.norm_real])
  have h' := h (-a - θ) (by linarith)
  rw [show θ + (-a - θ) = -a by ring] at h'
  exact (hc.congr' hf.symm EventuallyEq.rfl).trans h'

private lemma psiErr_isBigO_nhds_zero (b : ℝ) :
    psiErr =O[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t ^ (-b)) := by
  have : psiErr =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ => (0 : ℂ)) := by
    have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
      nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)
    filter_upwards [hlt] with t ht
    simp [psiErr, Set.indicator_of_notMem, not_lt.mpr ht.le]
  exact (isBigO_zero _ _).congr' this.symm EventuallyEq.rfl

private lemma LSeries_vonMangoldt_eq_mellin_psiErr {θ : ℝ} (hθ : θ < 1)
    (h : ∀ ε > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (θ + ε)))
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      s / (s - 1) + s * mellin psiErr (-s) := by
  rw [LSeries_vonMangoldt_eq_mul_integral_chebyshevPsi hs]
  have hind : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • psiErr t) =
      Set.indicator (Set.Ioi 1)
        (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Chebyshev.psi t - t : ℝ) : ℂ)) := by
    ext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;> simp [psiErr, Set.indicator, ht]
  have hmel : mellin psiErr (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Chebyshev.psi t - t : ℝ) : ℂ) := by
    rw [mellin, hind, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  have hconv : MellinConvergent psiErr (-s) :=
    mellinConvergent_of_isBigO_rpow (a := -1) (b := -s.re - 1) psiErr_locallyIntegrableOn
      (psiErr_isBigO h (by linarith)) (by simp; linarith)
      (psiErr_isBigO_nhds_zero _) (by simp)
  have hA : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Chebyshev.psi t - t : ℝ) : ℂ)) (Set.Ioi 1) := by
    refine (hconv.mono_set (Set.Ioi_subset_Ioi zero_le_one)).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    simp [psiErr, Set.indicator_of_mem ht]
  have hB : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), ((Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
      ∫ t in Set.Ioi (1 : ℝ),
        ((t : ℂ) ^ (-s - 1) * ((Chebyshev.psi t - t : ℝ) : ℂ) + (t : ℂ) ^ (-s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (t : ℂ) ≠ 0 := by
      have : (0 : ℝ) < t := lt_trans zero_lt_one ht
      exact_mod_cast this.ne'
    have hc : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s - 1) * t := by
      conv_lhs => rw [show -s = (-s - 1) + 1 by ring]
      rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
    rw [hc, Complex.ofReal_sub]
    ring
  have hint : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    have hs1 : s - 1 ≠ 0 := by
      intro h0
      have : (s - 1).re = 0 := by rw [h0]; simp
      simp at this
      linarith
    have hs1' : -s + 1 ≠ 0 := by
      intro h0; apply hs1; linear_combination -h0
    simp only [Complex.ofReal_one, Complex.one_cpow]
    field_simp
    ring
  rw [hsplit, integral_add hA hB, hint, hmel]
  ring

/-- **Error terms bound the zeros.** If `ψ(x) - x = O(x^{θ + ε})` as `x → ∞` for every `ε > 0`,
then `ζ(s)` has no zeros with `Re s > θ`. -/
theorem riemannZeta_ne_zero_of_forall_isBigO_rpow {θ : ℝ}
    (h : ∀ ε > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (θ + ε))) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  intro ρ hρ hζ
  have hρ1 : ρ.re < 1 := by
    by_contra hc
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hζ
  have hθ1 : θ < 1 := hρ.trans hρ1
  set c : ℝ := |ρ.im| / (1 - ρ.re) + 1 with hc
  set U : Set ℂ := {s : ℂ | θ < s.re ∧ c * (s.re - 1) < s.im} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (by fun_prop) Complex.continuous_im)
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    simp only [hU, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul] at hx hy ⊢
    obtain rfl : b = 1 - a := by linarith
    rcases ha.lt_or_eq with ha' | ha'
    · constructor
      · nlinarith [mul_lt_mul_of_pos_left hx.1 ha', mul_le_mul_of_nonneg_left hy.1.le hb]
      · nlinarith [mul_lt_mul_of_pos_left hx.2 ha', mul_le_mul_of_nonneg_left hy.2.le hb]
    · subst ha'
      simpa using hy
  have hρU : ρ ∈ U := by
    refine ⟨hρ, ?_⟩
    have h1 : 0 < 1 - ρ.re := by linarith
    have : c * (ρ.re - 1) = -|ρ.im| - (1 - ρ.re) := by
      rw [hc]; field_simp; ring
    rw [this]
    linarith [neg_abs_le ρ.im]
  have h1U : ∀ s ∈ U, s ≠ 1 := by
    rintro s hs rfl
    simp [hU] at hs
  -- the analytic continuation of `-ζ'/ζ`
  set G : ℂ → ℂ := fun s => s * mellin psiErr (-s) + s / (s - 1) with hG
  have hGd : DifferentiableOn ℂ G U := by
    intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (h1U s hs)
    have hre : θ < s.re := hs.1
    have hm : DifferentiableAt ℂ (mellin psiErr) (-s) :=
      mellin_differentiableAt_of_isBigO_rpow (a := -(s.re + θ) / 2)
        (b := -s.re - 1) psiErr_locallyIntegrableOn
        (psiErr_isBigO h (by linarith)) (by simp; linarith)
        (psiErr_isBigO_nhds_zero _) (by simp)
    have hm' : DifferentiableAt ℂ (fun s : ℂ => mellin psiErr (-s)) s :=
      hm.comp s differentiableAt_id.neg
    exact ((differentiableAt_id.mul hm').add
      (differentiableAt_id.div (differentiableAt_id.sub_const 1) hs1)).differentiableWithinAt
  have hζd : DifferentiableOn ℂ riemannZeta U := fun s hs =>
    (differentiableAt_riemannZeta (h1U s hs)).differentiableWithinAt
  have hζa : AnalyticOnNhd ℂ riemannZeta U := hζd.analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ G U := hGd.analyticOnNhd hUo
  set H : ℂ → ℂ := fun s => deriv riemannZeta s + riemannZeta s * G s with hH
  have hHa : AnalyticOnNhd ℂ H U := hζa.deriv.add (hζa.mul hGa)
  set z₀ : ℂ := 2 + ((c + 1 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀re : z₀.re = 2 := by simp [hz₀]
  have hz₀U : z₀ ∈ U := by
    refine ⟨by rw [hz₀re]; linarith, ?_⟩
    have : z₀.im = c + 1 := by simp [hz₀]
    rw [this, hz₀re]
    linarith
  have hHz : H =ᶠ[nhds z₀] 0 := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show 1 < z₀.re by rw [hz₀re]; norm_num)] with s hs
    have hs' : 1 < s.re := hs
    have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs'
    have hrep := LSeries_vonMangoldt_eq_mellin_psiErr hθ1 h hs'
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'] at hrep
    simp only [hH, hG, Pi.zero_apply]
    have : s * mellin psiErr (-s) + s / (s - 1) = -deriv riemannZeta s / riemannZeta s := by
      rw [hrep]; ring
    rw [this]
    field_simp
    ring
  have hH0 : Set.EqOn H 0 U := hHa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hUc.isPreconnected hz₀U hHz
  -- the order of vanishing at `ρ`
  have hζρ : AnalyticAt ℂ riemannZeta ρ := hζa ρ hρU
  have hord0 : analyticOrderAt riemannZeta z₀ ≠ ⊤ := by
    rw [(hζa z₀ hz₀U).analyticOrderAt_eq_zero.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by rw [hz₀re]; norm_num))]
    simp
  have hordρ : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    hζa.analyticOrderAt_ne_top_of_isPreconnected hUc.isPreconnected hz₀U hρU hord0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hordρ
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (analyticOrderAt_ne_zero.mpr ⟨hζρ, hζ⟩) hn.symm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hderiv : analyticOrderAt (deriv riemannZeta) ρ = m :=
    (analyticOrderAt_deriv_eq_iff hζρ hζ).mp (by rw [← hn]; push_cast; rfl)
  have heqd : deriv riemannZeta =ᶠ[nhds ρ] (riemannZeta * fun s => -G s) := by
    filter_upwards [hUo.mem_nhds hρU] with s hs
    have := hH0 hs
    simp only [hH, Pi.zero_apply] at this
    simp only [Pi.mul_apply]
    linear_combination this
  have hGρ : AnalyticAt ℂ (fun s => -G s) ρ := (hGa ρ hρU).neg
  have hmul := analyticOrderAt_mul hζρ hGρ
  rw [← analyticOrderAt_congr heqd, hderiv, ← hn] at hmul
  generalize analyticOrderAt (fun s => -G s) ρ = k at hmul
  cases k with
  | top => simp at hmul
  | coe k =>
    have : (m : ℕ∞) = ((m + 1 + k : ℕ) : ℕ∞) := by rw [hmul]; push_cast; rfl
    have := ENat.natCast_inj.mp this
    omega

/-- If `ψ(x) = x + O(x^{1/2} log² x)` as `x → ∞`, then `ζ(s)` has no zeros with `Re s > 1/2`.
This is the converse direction of von Koch's criterion for the Riemann hypothesis. -/
theorem riemannZeta_ne_zero_of_psi_sub_self_isBigO
    (h : (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => Real.sqrt x * Real.log x ^ 2)) :
    ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  refine riemannZeta_ne_zero_of_forall_isBigO_rpow fun ε hε => h.trans ?_
  have hlog : (fun x : ℝ => Real.log x ^ 2) =O[atTop] (fun x : ℝ => (x ^ (ε / 2)) ^ 2) :=
    ((isLittleO_log_rpow_atTop (by linarith)).pow two_pos).isBigO
  have hsq : (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) =O[atTop]
      (fun x : ℝ => Real.sqrt x * (x ^ (ε / 2)) ^ 2) :=
    (isBigO_refl (fun x : ℝ => Real.sqrt x) atTop).mul hlog
  refine hsq.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  push_cast
  ring
