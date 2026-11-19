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

namespace CSLibExtTest.MachineLearning.Sampling.PosteriorMonteCarloBetaBinomial

open MeasureTheory ProbabilityTheory
open Cslib.MachineLearning.Sampling Cslib.MachineLearning.Bayesian

/-- Use case: uniform prior, 10 trials, 7 successes. The posterior-mean estimate from exact
posterior draws is unbiased with variance `Var / m`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : ℝ → ℝ} (hg : Measurable g)
    (hg2 : MemLp g 2 (betaMeasure (1 + 7) (1 + (10 - 7 : ℕ))))
    {θs : ℕ → Ω → ℝ} (hθs : ∀ i, Measurable (θs i))
    (hlaw : ∀ i, μ.map (θs i) = betaMeasure (1 + 7) (1 + (10 - 7 : ℕ)))
    (hind : iIndepFun θs μ) {m : ℕ} (hm : m ≠ 0) :
    (∫ ω, mcEstimate g θs m ω ∂μ =
        ∫ θ, g θ ∂betaMeasure (1 + 7) (1 + (10 - 7 : ℕ))) ∧
      variance (mcEstimate g θs m) μ =
        variance g (betaMeasure (1 + 7) (1 + (10 - 7 : ℕ))) / m := by
  have ha : (0 : ℝ) < 1 := by norm_num
  have hb : (0 : ℝ) < 1 := by norm_num
  have hk : (7 : ℕ) ≤ 10 := by norm_num
  exact betaBinomial_posteriorMC_mean_variance ha hb hk hg hg2 hθs hlaw hind hm

/-- Positive evidence is attainable at `7 / 10` under the uniform prior. -/
example : (binomialKernel 10 ∘ₘ betaMeasure 1 1) {7} ≠ 0 := by
  have ha1 : (0 : ℝ) < 1 := by norm_num
  have hb1 : (0 : ℝ) < 1 := by norm_num
  rw [binomialKernel_comp_betaMeasure ha1 hb1]
  refine (ENNReal.ofReal_pos.mpr ?_).ne'
  have h1 := beta_pos (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have h2 := beta_pos (α := (1 : ℝ) + (7 : ℕ)) (β := (1 : ℝ) + (10 - 7 : ℕ))
    (by positivity) (by positivity)
  have h3 : (0 : ℝ) < Nat.choose 10 7 := by
    exact_mod_cast Nat.choose_pos (by norm_num : 7 ≤ 10)
  positivity

/-- Degenerate case: with no trials the posterior is the prior. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℝ} (hg : Measurable g)
    (hg2 : MemLp g 2 (betaMeasure (a + 0) (b + (0 - 0 : ℕ))))
    {θs : ℕ → Ω → ℝ} (hθs : ∀ i, Measurable (θs i))
    (hlaw : ∀ i, μ.map (θs i) = betaMeasure (a + 0) (b + (0 - 0 : ℕ)))
    (hind : iIndepFun θs μ) {m : ℕ} (hm : m ≠ 0) :
    variance (mcEstimate g θs m) μ =
      variance g (betaMeasure (a + 0) (b + (0 - 0 : ℕ))) / m := by
  have hk : (0 : ℕ) ≤ 0 := le_refl 0
  have h0 : (0 : ℝ) = ((0 : ℕ) : ℝ) := Nat.cast_zero.symm
  rw [h0] at hg2 hlaw ⊢
  exact (betaBinomial_posteriorMC_mean_variance ha hb hk hg hg2 hθs hlaw hind hm).2

/-- Square-integrability is attainable: the identity is in `L²` of `Beta(8, 4)`. -/
example : MemLp id 2 (betaMeasure (1 + 7) (1 + (10 - 7 : ℕ))) := by
  have h8 : (0 : ℝ) < 1 + 7 := by norm_num
  have hnn : (0 : ℝ) ≤ ((10 - 7 : ℕ) : ℝ) := by positivity
  have h4 : (0 : ℝ) < 1 + (10 - 7 : ℕ) := by linarith
  have hprob := isProbabilityMeasureBeta h8 h4
  have hpdf : Measurable (betaPDF (1 + 7) (1 + (10 - 7 : ℕ))) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal _ _)
  have hmem : ∀ᵐ x ∂(betaMeasure (1 + 7) (1 + (10 - 7 : ℕ))), id x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [betaMeasure, ae_withDensity_iff hpdf]
    filter_upwards with x hx
    show x ∈ Set.Icc (0 : ℝ) 1
    rw [Set.mem_Icc]
    rcases le_total 0 x with h0 | h0
    · rcases le_total x 1 with h1 | h1
      · exact ⟨h0, h1⟩
      · exact absurd (betaPDF_eq_zero_of_one_le h1) hx
    · exact absurd (betaPDF_eq_zero_of_nonpos h0) hx
  exact memLp_of_bounded hmem measurable_id.aestronglyMeasurable 2

end CSLibExtTest.MachineLearning.Sampling.PosteriorMonteCarloBetaBinomial
