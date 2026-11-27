/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-! # Barbălat's lemma for a convergent improper integral -/

open Filter MeasureTheory Set
open scoped Topology

namespace MetaMathlibExt

@[expose] public section

/-- **Barbălat's lemma.** Let $f : [0, \infty) \to \mathbb{R}$ be uniformly continuous. If
$\lim_{t \to \infty}\int_0^t f(s)\,ds$ exists as a finite real number, then $f(t) \to 0$
as $t \to \infty$. In Lean, `f` is defined on all of `ℝ`, but no regularity is assumed on
negative inputs.

Source: Bálint Farkas and Sven-Ake Wegner, *Variations on Barbălat's lemma*, American
Mathematical Monthly 123 (2016), Theorem 1 (arXiv:1411.1611). -/
theorem tendsto_zero_of_uniformContinuousOn_Ici_of_integral_tendsto
    {f : ℝ → ℝ} {L : ℝ} (hf : UniformContinuousOn f (Ici 0))
    (hlim : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hclose⟩ := Metric.uniformContinuousOn_iff.mp hf (ε / 2) (by linarith)
  let δ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have htol : 0 < ε * δ / 4 := by positivity
  let F (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, f s
  have htail : ∀ᶠ t in atTop, |F t - L| < ε * δ / 4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hlim _ htol
  obtain ⟨T, hT⟩ := eventually_atTop.1 htail
  refine eventually_atTop.2 ⟨max T 0, fun t ht => ?_⟩
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htδ : t ≤ t + δ := by linarith
  have hInt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab <|
      hf.continuousOn.mono (show Icc a b ⊆ Ici 0 from fun _ hx => ha.trans hx.1)
  let I := ∫ s in t..t + δ, f s
  -- The integral over the short interval is the difference of two tail values.
  have hI : I = F (t + δ) - F t :=
    (intervalIntegral.integral_interval_sub_left
      (hInt le_rfl (ht₀.trans htδ)) (hInt le_rfl ht₀)).symm
  have htnear := abs_lt.mp (hT t htT)
  have htδnear := abs_lt.mp (hT (t + δ) (htT.trans htδ))
  have hsmall₁ : -(ε * δ / 2) < I := by rw [hI]; linarith only [htnear.2, htδnear.1]
  have hsmall₂ : I < ε * δ / 2 := by rw [hI]; linarith only [htnear.1, htδnear.2]
  -- Uniform continuity sandwiches the average over the interval around `f t`.
  have hbracket (s : ℝ) (hs : s ∈ Icc t (t + δ)) :
      f t - ε / 2 ≤ f s ∧ f s ≤ f t + ε / 2 := by
    have hdist : dist s t < η := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      have hright := hs.2
      dsimp [δ] at hright
      linarith only [hright, hη]
    have h := hclose s (ht₀.trans hs.1) t ht₀ hdist
    rw [Real.dist_eq, abs_lt] at h
    constructor <;> linarith only [h.1, h.2]
  have hlo := intervalIntegral.integral_mono_on htδ intervalIntegrable_const (hInt ht₀ htδ)
    (fun s hs => (hbracket s hs).1)
  have hhi := intervalIntegral.integral_mono_on htδ (hInt ht₀ htδ) intervalIntegrable_const
    (fun s hs => (hbracket s hs).2)
  simp only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] at hlo hhi
  change δ * (f t - ε / 2) ≤ I at hlo
  change I ≤ δ * (f t + ε / 2) at hhi
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor
  · apply (mul_lt_mul_iff_right₀ hδ).mp
    nlinarith only [hsmall₁, hhi]
  · apply (mul_lt_mul_iff_right₀ hδ).mp
    nlinarith only [hsmall₂, hlo]

end

end MetaMathlibExt
