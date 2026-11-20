/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Resampling.BootstrapQuantile
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Tests for weak-convergence-to-quantile

The generalized inverse computes on a Dirac law (median of `dirac 0` is `0`), and the
Dirac CDF discontinuity at `0` shows Dirac laws fall outside the stated hypotheses
(no necessity is claimed: this does not show that dropping continuity breaks
quantile convergence in general). The new convergence theorem is covered by a generic
signature application and a concrete standard-normal non-vacuity example.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

-- Positive/use: the generalized inverse computes on a Dirac law (median of dirac 0 is 0).
example : ProbabilityTheory.cdfQuantile (Measure.dirac (0 : ℝ)) (1 / 2) = 0 := by
  unfold cdfQuantile
  have hmem : ((1 : ℝ) / 2) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  simp only [hmem, ↓reduceIte]
  have hset : {x : ℝ | ((1 : ℝ) / 2) ≤ cdf (Measure.dirac (0 : ℝ)) x} = Set.Ici 0 := by
    ext x
    simp only [Set.mem_Ici]
    show (((1 : ℝ) / 2) ≤ cdf (Measure.dirac (0 : ℝ)) x) ↔ _
    rw [cdf_eq_real]
    rw [Measure.dirac_real_apply]
    simp only [Set.indicator_apply, Pi.one_apply]
    by_cases hx : (0 : ℝ) ∈ Set.Iic x
    · simp only [hx, ↓reduceIte]
      have hx0 : (0 : ℝ) ≤ x := Set.mem_Iic.mp hx
      simp only [hx0, iff_true]
      norm_num
    · simp only [hx, ↓reduceIte]
      have hnx : ¬ (0 : ℝ) ≤ x := fun h => hx (Set.mem_Iic.mpr h)
      simp only [hnx, iff_false]
      norm_num
  rw [hset, csInf_Ici]

-- Boundary: the Dirac CDF is discontinuous at 0, so Dirac laws lie outside the stated
-- assumptions (no necessity claim: continuity is sufficient, not shown necessary).
example : ¬ Continuous (fun x : ℝ => (Measure.dirac (0 : ℝ)).real (Set.Iic x)) := by
  intro hcont
  have hF0 : (Measure.dirac (0 : ℝ)).real (Set.Iic 0) = 1 := by
    simp
  have hseq : Filter.Tendsto (fun n : ℕ => (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.neg
    simpa using h2
  have hcomp : Filter.Tendsto (fun n : ℕ => (Measure.dirac (0 : ℝ)).real (Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ))) atTop (𝓝 ((Measure.dirac (0 : ℝ)).real (Set.Iic 0))) :=
    (hcont.tendsto 0).comp hseq
  have hzero : ∀ n : ℕ, (Measure.dirac (0 : ℝ)).real (Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ)) = 0 := by
    intro n
    rw [Measure.dirac_real_apply]
    simp only [Set.indicator_apply, Pi.one_apply]
    have hneg : (0 : ℝ) ∉ Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ) := by
      simp only [Set.mem_Iic, not_le]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    simp only [hneg, ↓reduceIte]
  have hconst : Filter.Tendsto (fun n : ℕ => (Measure.dirac (0 : ℝ)).real (Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ))) atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hcomp hconst
  rw [hF0] at heq
  norm_num at heq

-- Coverage: the new theorem applies under its generic hypotheses, pinning its public
-- name and signature. Both `TendstoInDistribution` and the theorem are referenced.
example {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hw : TendstoInDistribution X atTop Y (fun _ => μ) μ')
    {F : ℝ → ℝ} (hF : ∀ x, F x = (Measure.map Y μ').real (Set.Iic x))
    (hcont : Continuous F) (hstrict : StrictMono F)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n => cdfQuantile (Measure.map (X n) μ) q) atTop
      (𝓝 (cdfQuantile (Measure.map Y μ') q)) :=
  tendsto_cdfQuantile_of_tendstoInDistribution hw hF hcont hstrict hq

-- Concrete non-vacuity: the standard normal limit has a continuous strictly increasing
-- CDF (no atoms; every `(a, b]` carries positive mass via the density), so the theorem
-- gives quantile convergence for a constant standard-normal sequence.
example {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun _ : ℕ => cdfQuantile (gaussianReal 0 1) q) atTop
      (𝓝 (cdfQuantile (gaussianReal 0 1) q)) := by
  have hsing : ∀ a : ℝ, (gaussianReal 0 1) {a} = 0 :=
    fun a => (nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero).measure_singleton a
  have hmono : Monotone ⇑(cdf (gaussianReal 0 1)) := monotone_cdf _
  have hcont : Continuous fun x => (gaussianReal 0 1).real (Set.Iic x) := by
    have heq : (fun x => (gaussianReal 0 1).real (Set.Iic x)) = ⇑(cdf (gaussianReal 0 1)) :=
      funext fun x => (cdf_eq_real _ x).symm
    rw [heq, continuous_iff_continuousAt]
    intro a
    rw [hmono.continuousAt_iff_leftLim_eq_rightLim, (cdf (gaussianReal 0 1)).rightLim_eq a]
    have hmeas : (cdf (gaussianReal 0 1)).measure {a} = 0 := by
      rw [measure_cdf]; exact hsing a
    have hsingle := StieltjesFunction.measure_singleton (cdf (gaussianReal 0 1)) a
    rw [hmeas] at hsingle
    have hle : (cdf (gaussianReal 0 1)) a - Function.leftLim ⇑(cdf (gaussianReal 0 1)) a ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hsingle.symm
    have hge : Function.leftLim ⇑(cdf (gaussianReal 0 1)) a ≤ (cdf (gaussianReal 0 1)) a :=
      hmono.leftLim_le le_rfl
    linarith
  have hstrict : StrictMono fun x => (gaussianReal 0 1).real (Set.Iic x) := by
    have hpdf : ∀ x : ℝ, 0 < gaussianPDFReal 0 1 x :=
      fun x => gaussianPDFReal_pos 0 1 x one_ne_zero
    have hpdfcont : Continuous (gaussianPDFReal 0 1) := by
      unfold gaussianPDFReal; fun_prop
    intro a b hab
    have hI : (0 : ℝ) < ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (ae_of_all _ fun x => le_of_lt (hpdf x)) hpdfcont.integrableOn_Ioc]
      have hsup : Function.support (gaussianPDFReal 0 1) = Set.univ :=
        Set.eq_univ_iff_forall.mpr fun x => Function.mem_support.mpr (hpdf x).ne'
      rw [hsup, Set.univ_inter, Real.volume_Ioc]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    have hIoc : (gaussianReal 0 1) (Set.Ioc a b)
        = ENNReal.ofReal ((cdf (gaussianReal 0 1)) b - (cdf (gaussianReal 0 1)) a) := by
      have h := (cdf (gaussianReal 0 1)).measure_Ioc a b
      rwa [measure_cdf] at h
    have hreal : (gaussianReal 0 1).real (Set.Ioc a b)
        = (cdf (gaussianReal 0 1)) b - (cdf (gaussianReal 0 1)) a := by
      rw [measureReal_def, hIoc, ENNReal.toReal_ofReal]
      exact sub_nonneg.mpr (hmono (le_of_lt hab))
    have hIocreal : (gaussianReal 0 1).real (Set.Ioc a b)
        = ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x := by
      have h := gaussianReal_apply_eq_integral (0 : ℝ) (v := 1) one_ne_zero (Set.Ioc a b)
      rw [measureReal_def, h, ENNReal.toReal_ofReal]
      exact setIntegral_nonneg measurableSet_Ioc (fun x _ => le_of_lt (hpdf x))
    have hpos : (0 : ℝ) < (gaussianReal 0 1).real (Set.Ioc a b) := by
      rwa [hIocreal]
    have hlt : (cdf (gaussianReal 0 1)) a < (cdf (gaussianReal 0 1)) b :=
      sub_pos.mp (hreal ▸ hpos)
    show (gaussianReal 0 1).real (Set.Iic a) < (gaussianReal 0 1).real (Set.Iic b)
    rwa [← cdf_eq_real (gaussianReal 0 1) a, ← cdf_eq_real (gaussianReal 0 1) b]
  have hw : TendstoInDistribution (fun _ : ℕ => (id : ℝ → ℝ)) atTop id
      (fun _ => gaussianReal 0 1) (gaussianReal 0 1) :=
    tendstoInDistribution_const (μ' := gaussianReal 0 1) measurable_id.aemeasurable
  have hF : ∀ x, (fun x => (gaussianReal 0 1).real (Set.Iic x)) x
      = (Measure.map id (gaussianReal 0 1)).real (Set.Iic x) := by
    intro x
    show (gaussianReal 0 1).real (Set.Iic x) = _
    rw [Measure.map_id]
  have hmain := tendsto_cdfQuantile_of_tendstoInDistribution
    (F := fun x => (gaussianReal 0 1).real (Set.Iic x)) hw hF hcont hstrict hq
  simpa only [Measure.map_id] using hmain
