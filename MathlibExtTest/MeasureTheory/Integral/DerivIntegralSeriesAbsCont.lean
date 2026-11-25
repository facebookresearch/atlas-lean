/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Integral.DerivIntegralSeriesAbsCont
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open MathlibExt.MeasureTheory.DerivIntegralSeriesAbsContWanted

private noncomputable def affineSeries (n : ℕ) (_ : Fin 0 → ℝ) : ℝ → ℂ :=
  if n = 0 then (fun t : ℝ => t • Complex.I) else fun _ => 0

-- In dimension zero the spatial measure has mass one. The nonzero imaginary derivative tests
-- the complex FTC, not just the real part, on both sides of the interior anchor 1.
example : ∃ F : ℝ → ℂ, ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) 2)),
    HasDerivAt F Complex.I y := by
  let μ := (volume : Measure (Fin 0 → ℝ)).restrict univ
  let ν := (volume : Measure ℝ).restrict (Ioo 0 2)
  have hμ : μ = Measure.dirac (fun i : Fin 0 => Fin.elim0 i) := by
    change (volume : Measure (Fin 0 → ℝ)).restrict univ = _
    rw [Measure.restrict_univ]
    exact Measure.volume_pi_eq_dirac _
  let : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioo]; simp)
  have hd (n : ℕ) (x : Fin 0 → ℝ) (y : ℝ) :
      deriv (affineSeries n x) y = if n = 0 then Complex.I else 0 := by
    by_cases hn : n = 0
    · rw [affineSeries, ite_eq_left hn, ite_eq_left hn]
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id y).smul_const (𝕜' := ℝ) Complex.I).deriv
    · rw [affineSeries, ite_eq_right hn, ite_eq_right hn, deriv_const]
  have hnorm (n : ℕ) (x : Fin 0 → ℝ) (y : ℝ) :
      ‖deriv (affineSeries n x) y‖ = if n = 0 then (1 : ℝ) else 0 := by
    by_cases hn : n = 0 <;> simp [hd, hn]
  have hanchor (n : ℕ) (x : Fin 0 → ℝ) :
      ‖affineSeries n x 1‖ = if n = 0 then (1 : ℝ) else 0 := by
    by_cases hn : n = 0 <;> simp [affineSeries, hn]
  have hsum : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    exact ite_eq_right hn
  have hone : (∑' n : ℕ, if n = 0 then (1 : ℝ) else 0) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [hn]
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun p : (Fin 0 → ℝ) × ℝ => affineSeries n p.1 p.2) (μ.prod ν) := by
    by_cases hn : n = 0
    · simpa only [affineSeries, ite_eq_left hn] using
        (continuous_snd.fun_smul continuous_const : Continuous fun p : (Fin 0 → ℝ) × ℝ =>
          p.2 • Complex.I).aestronglyMeasurable
    · simp only [affineSeries, ite_eq_right hn]
      exact aestronglyMeasurable_const
  have hac (n : ℕ) : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (affineSeries n x) 0 2 := by
    filter_upwards with x
    have h : ContDiff ℝ 1 (affineSeries n x) := by
      by_cases hn : n = 0
      · rw [affineSeries, ite_eq_left hn]
        exact (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ)).smul_const (A := ℝ) Complex.I
      · rw [affineSeries, ite_eq_right hn]
        exact contDiff_const
    exact h.contDiffOn.absolutelyContinuousOnInterval
  have hdm (n : ℕ) : AEStronglyMeasurable (fun p : (Fin 0 → ℝ) × ℝ =>
      deriv (affineSeries n p.1) p.2) (μ.prod ν) := by
    simp_rw [hd]
    exact aestronglyMeasurable_const
  have hds : ∀ᵐ p : (Fin 0 → ℝ) × ℝ ∂(μ.prod ν),
      Summable (fun n => ‖deriv (affineSeries n p.1) p.2‖) := by
    simp_rw [hnorm]
    exact Eventually.of_forall fun _ => hsum
  have hdi : Integrable (fun p : (Fin 0 → ℝ) × ℝ => ∑' n, ‖deriv (affineSeries n p.1) p.2‖)
      (μ.prod ν) := by
    simp_rw [hnorm, hone]
    exact integrable_const 1
  have hcs : ∀ᵐ x ∂μ, Summable (fun n => ‖affineSeries n x 1‖) := by
    simp_rw [hanchor]
    exact Eventually.of_forall fun _ => hsum
  have hci : Integrable (fun x => ∑' n, ‖affineSeries n x 1‖) μ := by
    simp_rw [hanchor, hone]
    exact integrable_const 1
  obtain ⟨F, -, -, hF⟩ := exists_hasDerivAt_integral_tsum_ae (d := 0) univ isOpen_univ 0 2 1
    (by norm_num) (by norm_num) (by norm_num) affineSeries hm hac hdm hds hdi hcs hci
  refine ⟨F, hF.mono fun y hy => ?_⟩
  have hvalue : (∑' n, ∫ x, deriv (affineSeries n x) y ∂μ) = Complex.I := by
    rw [tsum_eq_single 0]
    · simp [hd, hμ]
    · intro n hn; simp [hd, hn]
  exact hvalue ▸ hy
