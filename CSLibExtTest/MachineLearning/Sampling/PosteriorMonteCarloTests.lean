/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.PosteriorMonteCarlo
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# Tests for posterior Monte Carlo error
-/

set_option autoImplicit false

namespace CSLibExtTest.MachineLearning.Sampling.PosteriorMonteCarlo

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Sampling Cslib.MachineLearning.Bayesian

/-- A fair coin on `Bool`. -/
private noncomputable def coin : Measure Bool :=
  (1 / 2 : NNReal) • Measure.dirac true + (1 / 2 : NNReal) • Measure.dirac false

private instance : IsProbabilityMeasure coin := by
  constructor
  simp [coin, ENNReal.inv_two_add_inv_two]

/-- One draw: the Monte Carlo variance is the integrand's variance. -/
example {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {ν : Measure α}
    {f : α → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 ν) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν) (hind : iIndepFun X μ) :
    variance (mcEstimate f X 1) μ = variance f ν := by
  rw [variance_mcEstimate hf hf2 hX hlaw hind one_ne_zero, Nat.cast_one, div_one]

/-- Positive evidence is attainable: the constant-likelihood model with the fair-coin prior. -/
example : (Kernel.const Bool (Measure.dirac true) ∘ₘ coin) {true} ≠ 0 := by
  rw [Measure.const_comp, measure_univ, one_smul]
  simp

/-- Every hypothesis realized with a non-degenerate posterior: with a likelihood that ignores
`θ` the posterior is the fair-coin prior, and i.i.d. coordinates under `Measure.infinitePi` are
exact posterior draws. Derive this from `mcEstimate_bayesPosterior_mean_variance`. -/
example (g : Bool → ℝ) {m : ℕ} (hm : m ≠ 0) :
    variance (mcEstimate g (fun i (ω : ℕ → Bool) => ω i) m)
        (Measure.infinitePi fun _ : ℕ => coin) =
      variance g (bayesPosterior (Kernel.const Bool (Measure.dirac true)) coin true) / m := by
  have hx : (Kernel.const Bool (Measure.dirac true) ∘ₘ coin) {true} ≠ 0 := by
    rw [Measure.const_comp, measure_univ, one_smul]
    simp
  have hpost : bayesPosterior (Kernel.const Bool (Measure.dirac true)) coin true = coin := by
    rw [bayesPosterior, Measure.const_comp, measure_univ, one_smul]
    simp
  exact (mcEstimate_bayesPosterior_mean_variance (μ := Measure.infinitePi fun _ : ℕ => coin)
    (Kernel.const Bool (Measure.dirac true)) coin hx (g := g) Measurable.of_discrete
    (by rw [hpost]; exact MemLp.of_discrete) (θs := fun i (ω : ℕ → Bool) => ω i)
    (fun i ↦ measurable_pi_apply i) (fun i ↦ by rw [hpost]; exact Measure.infinitePi_map_eval _ i)
    (iIndepFun_infinitePi fun _ ↦ measurable_id) hm).2

/-- Infinite-variance boundary, law: the uniform law on `(0, 1)`,
`ν = volume.restrict (Set.Ioo 0 1)`, is a probability measure. -/
example : IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num

/-- Infinite-variance boundary, integrand: `f x = x ^ (-1/2)` (real power) is measurable. -/
example : Measurable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := by
  exact measurable_id.pow_const _

/-- Infinite-variance boundary: `f x = x ^ (-1/2)` is not square-integrable under the uniform
law on `(0, 1)` (`f x ^ 2 = x ^ (-1)` there), so `MemLp f 2 ν` fails and neither pinned theorem
applies to it. -/
example : ¬ MemLp (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 2 (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  intro h
  have hmeas : Measurable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) := measurable_id.pow_const _
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable] at h
  have h' : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Set.Ioo 0 1) := by
    refine IntegrableOn.congr_fun h (fun x hx ↦ ?_) measurableSet_Ioo
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    norm_num
  exact lt_irrefl _ ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp h')

end CSLibExtTest.MachineLearning.Sampling.PosteriorMonteCarlo

#print axioms Cslib.MachineLearning.Sampling.variance_mcEstimate
#print axioms Cslib.MachineLearning.Sampling.mcEstimate_bayesPosterior_mean_variance
