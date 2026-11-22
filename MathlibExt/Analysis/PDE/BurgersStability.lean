/-
Copyright (c) 2025–2026 the contributors.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.BurgersComparison
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# L¹ contraction for the Burgers evolution

For bounded continuous initial velocities with integrable difference, the
velocity difference remains integrable and its L¹ norm does not increase.
The ordered case uses a bounded logarithmic primitive of the difference.
General data are enclosed by the evolutions of their pointwise minimum and maximum.

Reference: Gallay and Scheel, *Viscous shocks and long-time behavior of scalar
conservation laws*, Section 2,
https://www-fourier.univ-grenoble-alpes.fr/~gallay/ScalarCL.pdf.
-/

@[expose] public section

open MeasureTheory Set Filter Real
open scoped Topology
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

private theorem integrable_of_bounded_primitive {w Q : ℝ → ℝ} {A B : ℝ}
    (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) (hd : ∀ x, HasDerivAt Q (w x) x)
    (hQ : ∀ x, Q x ∈ Icc A B) : Integrable w ∧ (∫ x, w x) ≤ B - A := by
  have he (a b : ℝ) : (∫ x in a..b, w x) = Q b - Q a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hw.intervalIntegrable a b)
  have hi : Integrable w := integrable_of_intervalIntegral_norm_bounded (B - A)
    (fun r : ℝ => hw.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    tendsto_neg_atTop_atBot tendsto_id (Eventually.of_forall (fun r => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
      rw [he]
      exact sub_le_sub (hQ r).2 (hQ (-r)).1))
  refine ⟨hi, le_of_tendsto
    (intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id) ?_⟩
  exact Eventually.of_forall (fun r => by rw [he]; exact sub_le_sub (hQ r).2 (hQ (-r)).1)

/-- For ordered data the nonnegative velocity difference remains integrable,
and its integral does not increase. -/
theorem burgersSolution_ordered_integral_le {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν t : ℝ} (hν : 0 < ν) (h : ∀ x, u x ≤ v x)
    (hi : Integrable (fun x => v x - u x)) (a : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution ν v a t x - burgersSolution ν u a t x) ∧
      (∫ x, burgersSolution ν v a t x - burgersSolution ν u a t x) ≤ ∫ x, v x - u x := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simpa only [burgersSolution_zero hu hν.ne', burgersSolution_zero hv hν.ne'] using
      And.intro hi (le_refl (∫ x, v x - u x))
  let f := initialHeatProfile ν u a
  let g := initialHeatProfile ν v a
  let F := fun x => ∫ y in Iic x, (v y - u y)
  let D := ∫ y, v y - u y
  have hF (x : ℝ) : F x ∈ Icc 0 D :=
    ⟨integral_nonneg (fun y => sub_nonneg.mpr (h y)),
      setIntegral_le_integral hi (ae_of_all _ (fun y => sub_nonneg.mpr (h y)))⟩
  have he (x : ℝ) : f x = exp ((F x - F a) / (2 * ν)) * g x := by
    have hh := intervalIntegral.integral_Iic_sub_Iic (hi.integrableOn (s := Iic a))
      (hi.integrableOn (s := Iic x))
    change exp (-(∫ y in a..x, u y) / (2 * ν)) =
      exp (((∫ y in Iic x, v y - u y) - ∫ y in Iic a, v y - u y) / (2 * ν)) *
        exp (-(∫ y in a..x, v y) / (2 * ν))
    rw [hh, intervalIntegral.integral_sub (hv.intervalIntegrable a x) (hu.intervalIntegrable a x),
      ← exp_add]
    congr 1
    ring
  let A := exp (-F a / (2 * ν))
  let B := exp ((D - F a) / (2 * ν))
  have hA : 0 < A := exp_pos _
  have hB : 0 < B := exp_pos _
  have hfg (x : ℝ) : A * g x ≤ f x ∧ f x ≤ B * g x := by
    rw [he]
    have hgx := (initialHeatProfile_pos ν v a x).le
    constructor
    · apply mul_le_mul_of_nonneg_right _ hgx
      apply exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (mul_pos (by norm_num) hν).le
      linarith [(hF x).1]
    · apply mul_le_mul_of_nonneg_right _ hgx
      apply exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (sub_le_sub_right (hF x).2 _) (by positivity)
  have hf := (initialHeatProfile_contDiff hu ν a).continuous
  have hg := (initialHeatProfile_contDiff hv ν a).continuous
  have hgf := initialHeatProfile_hasExpGrowth hbu hν a
  have hgg := initialHeatProfile_hasExpGrowth hbv hν a
  let Hf := heatSolution f (ν * t)
  let Hg := heatSolution g (ν * t)
  have hpf (x : ℝ) : 0 < Hf x :=
    heatSolution_pos_of_exp_growth hf hgf (initialHeatProfile_pos ν u a) (ν * t) x
  have hpg (x : ℝ) : 0 < Hg x :=
    heatSolution_pos_of_exp_growth hg hgg (initialHeatProfile_pos ν v a) (ν * t) x
  have hheat (x : ℝ) : A * Hg x ≤ Hf x ∧ Hf x ≤ B * Hg x := by
    constructor
    · have hh := heatSolution_mono_of_exp_growth (continuous_const.mul hg).aestronglyMeasurable
        hf.aestronglyMeasurable (hgg.const_mul A) hgf (fun y => (hfg y).1) (ν * t) x
      change heatSolution (fun y => A * g y) (ν * t) x ≤ Hf x at hh
      simpa only [heatSolution_const_mul] using hh
    · have hh := heatSolution_mono_of_exp_growth hf.aestronglyMeasurable
        (continuous_const.mul hg).aestronglyMeasurable hgf (hgg.const_mul B)
        (fun y => (hfg y).2) (ν * t) x
      change Hf x ≤ heatSolution (fun y => B * g y) (ν * t) x at hh
      simpa only [heatSolution_const_mul] using hh
  let Q := fun x => 2 * ν * (log (Hf x) - log (Hg x))
  have hQ (x : ℝ) : Q x ∈ Icc (-F a) (D - F a) := by
    have hlo := log_le_log (mul_pos hA (hpg x)) (hheat x).1
    have hhi := log_le_log (hpf x) (hheat x).2
    rw [log_mul hA.ne' (hpg x).ne'] at hlo
    rw [log_mul hB.ne' (hpg x).ne'] at hhi
    dsimp [A, B] at hlo hhi
    rw [log_exp] at hlo hhi
    have hden : 0 < 2 * ν := by positivity
    have hl := (div_le_iff₀ hden).mp (show -F a / (2 * ν) ≤ log (Hf x) - log (Hg x) by
      linarith)
    have hr := (le_div_iff₀ hden).mp (show log (Hf x) - log (Hg x) ≤ (D - F a) / (2 * ν) by
      linarith)
    dsimp [Q]
    constructor <;> nlinarith
  have hd (x : ℝ) : HasDerivAt Q
      (burgersSolution ν v a t x - burgersSolution ν u a t x) x := by
    have hdf := heatSolution_hasDerivAt_space_of_exp_growth hf.aestronglyMeasurable hgf
      (mul_pos hν ht) x
    have hdg := heatSolution_hasDerivAt_space_of_exp_growth hg.aestronglyMeasurable hgg
      (mul_pos hν ht) x
    have hlog := ((hdf.log (hpf x).ne').sub (hdg.log (hpg x).ne')).const_mul (2 * ν)
    convert hlog using 1
    change -2 * ν * (deriv (heatSolution g (ν * t)) x / Hg x) -
      (-2 * ν * (deriv (heatSolution f (ν * t)) x / Hf x)) = _
    rw [hdf.deriv, hdg.deriv]
    ring
  have hc : Continuous (fun x => burgersSolution ν v a t x - burgersSolution ν u a t x) :=
    ((burgersSolution_continuous_of_bounded hv hbv hν a).comp
      (continuous_const.prodMk continuous_id)).sub
      ((burgersSolution_continuous_of_bounded hu hbu hν a).comp
        (continuous_const.prodMk continuous_id))
  have hh := integrable_of_bounded_primitive hc
    (fun x => sub_nonneg.mpr (burgersSolution_mono hu hv hbu hbv hν h a ht.le x)) hd hQ
  simpa only [sub_neg_eq_add, sub_add_cancel] using hh

/-- The Burgers evolution is an L¹ contraction on integrable differences of bounded continuous data.
The individual initial velocities need not be integrable. -/
theorem burgersSolution_l1_contraction {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν t : ℝ} (hν : 0 < ν) (hi : Integrable (fun x => u x - v x))
    (a : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution ν u a t x - burgersSolution ν v a t x) ∧
      (∫ x, |burgersSolution ν u a t x - burgersSolution ν v a t x|) ≤ ∫ x, |u x - v x| := by
  let lo := fun x => min (u x) (v x)
  let up := fun x => max (u x) (v x)
  obtain ⟨Mu, hMu⟩ := hbu
  obtain ⟨Mv, hMv⟩ := hbv
  have hbmin : ∃ M, ∀ x, |lo x| ≤ M := by
    refine ⟨max Mu Mv, fun x => ?_⟩
    rcases le_total (u x) (v x) with h | h
    · simpa only [lo, min_eq_left h] using (hMu x).trans (le_max_left Mu Mv)
    · simpa only [lo, min_eq_right h] using (hMv x).trans (le_max_right Mu Mv)
  have hbmax : ∃ M, ∀ x, |up x| ≤ M := by
    refine ⟨max Mu Mv, fun x => ?_⟩
    rcases le_total (u x) (v x) with h | h
    · simpa only [up, max_eq_right h] using (hMv x).trans (le_max_right Mu Mv)
    · simpa only [up, max_eq_left h] using (hMu x).trans (le_max_left Mu Mv)
  have heq (x : ℝ) : up x - lo x = |u x - v x| := by
    dsimp [up, lo]
    rw [max_sub_min_eq_abs, abs_sub_comm]
  have hi' : Integrable (fun x => up x - lo x) := by
    simpa only [heq] using! hi.abs
  have hord := burgersSolution_ordered_integral_le (hu.min hv) (hu.max hv) hbmin hbmax hν
    (fun x => (min_le_left (u x) (v x)).trans (le_max_left (u x) (v x))) hi' a ht
  have hbound (x : ℝ) : |burgersSolution ν u a t x - burgersSolution ν v a t x| ≤
      burgersSolution ν up a t x - burgersSolution ν lo a t x := by
    have h1 := burgersSolution_mono (hu.min hv) hu hbmin ⟨Mu, hMu⟩ hν
      (fun y => min_le_left (u y) (v y)) a ht x
    have h2 := burgersSolution_mono (hu.min hv) hv hbmin ⟨Mv, hMv⟩ hν
      (fun y => min_le_right (u y) (v y)) a ht x
    have h3 := burgersSolution_mono hu (hu.max hv) ⟨Mu, hMu⟩ hbmax hν
      (fun y => le_max_left (u y) (v y)) a ht x
    have h4 := burgersSolution_mono hv (hu.max hv) ⟨Mv, hMv⟩ hbmax hν
      (fun y => le_max_right (u y) (v y)) a ht x
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : Continuous (fun x => burgersSolution ν u a t x - burgersSolution ν v a t x) :=
    ((burgersSolution_continuous_of_bounded hu ⟨Mu, hMu⟩ hν a).comp
      (continuous_const.prodMk continuous_id)).sub
      ((burgersSolution_continuous_of_bounded hv ⟨Mv, hMv⟩ hν a).comp
        (continuous_const.prodMk continuous_id))
  have hiout := hord.1.mono' hc.aestronglyMeasurable (ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs] using hbound x))
  refine ⟨hiout, (integral_mono hiout.abs hord.1 hbound).trans ?_⟩
  have hh : (∫ x, burgersSolution ν up a t x - burgersSolution ν lo a t x) ≤
      ∫ x, up x - lo x := hord.2
  simpa only [heq] using hh

/-- L¹ contraction is independent of the two spatial normalization anchors. -/
theorem burgersSolution_l1_contraction_of_anchors {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν t : ℝ} (hν : 0 < ν) (hi : Integrable (fun x => u x - v x))
    (a b : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => burgersSolution ν u a t x - burgersSolution ν v b t x) ∧
      (∫ x, |burgersSolution ν u a t x - burgersSolution ν v b t x|) ≤ ∫ x, |u x - v x| := by
  simp_rw [burgersSolution_anchor_independent hv hbv hν b a t _ ht]
  exact burgersSolution_l1_contraction hu hv hbu hbv hν hi a ht

end ColeHopf
