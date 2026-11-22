/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Generative.BayesClassifier

/-!
# Tests for the Bayes classifier

* The 0-1 loss is `0` on the true class and `1` elsewhere.
* Noise-free observations (`P c = δ_c`): the identity classifier never errs, and the constant
  classifier `false` errs with probability `π {true}`.
* For two classes a posterior argmax classifier exists and attains the Bayes risk, and a
  classifier picking maximum a posteriori classes from countable observations beats every
  randomized classifier.
-/

@[expose] public section

namespace Cslib.MachineLearning.BayesClassifierTests

open Cslib.MachineLearning BayesClassifier MeasureTheory ProbabilityTheory
open scoped ENNReal

example : zeroOneLoss true true = 0 := by simp [zeroOneLoss_apply]

example : zeroOneLoss true false = 1 := by simp [zeroOneLoss_apply]

/-- Noise-free observations: the class is observed directly. -/
noncomputable def P₀ : Kernel Bool Bool := Kernel.deterministic id measurable_id

example (π : Measure Bool) :
    avgRisk zeroOneLoss P₀ (Kernel.deterministic id measurable_id) π = 0 := by
  rw [avgRisk_zeroOneLoss_deterministic]
  simp [P₀, Kernel.deterministic_apply]

example (π : Measure Bool) :
    avgRisk zeroOneLoss P₀
      (Kernel.deterministic _ (measurable_const : Measurable fun _ : Bool => false)) π =
      π {true} := by
  rw [avgRisk_zeroOneLoss_deterministic]
  have h : ∀ c : Bool,
      P₀ c {x | (fun _ : Bool => false) x ≠ c} = ({true} : Set Bool).indicator 1 c := by
    intro c
    cases c <;> simp [P₀, Kernel.deterministic_apply]
  simp_rw [h]
  rw [lintegral_indicator_one (measurableSet_singleton true)]

example (P : Kernel Bool Bool) [IsMarkovKernel P] (π : Measure Bool) [IsFiniteMeasure π] :
    ∃ f : Kernel Bool Bool, IsBayesEstimator zeroOneLoss P f π := by
  obtain ⟨f, hf⟩ := exists_isPosteriorArgmax P π
  exact ⟨_, hf.isBayesEstimator⟩

example (P : Kernel Bool ℕ) [IsMarkovKernel P] (π : Measure Bool) [IsFiniteMeasure π]
    (f : ℕ → Bool) (hf : ∀ x, (P ∘ₘ π) {x} ≠ 0 → Bayesian.IsMAP P π x (f x))
    (κ : Kernel ℕ Bool)
    [IsMarkovKernel κ] :
    avgRisk zeroOneLoss P (Kernel.deterministic f (measurable_of_countable f)) π ≤
      avgRisk zeroOneLoss P κ π :=
  (isPosteriorArgmax_of_isMAP hf).avgRisk_le κ

example (P : Kernel Bool Bool) [IsMarkovKernel P] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesRisk zeroOneLoss P π = ∫⁻ x, ⨅ y, (P†π) x {y}ᶜ ∂(P ∘ₘ π) :=
  bayesRisk_zeroOneLoss P π

end Cslib.MachineLearning.BayesClassifierTests

namespace CSLibExtTest.MachineLearning.Generative.BayesClassifier

open MeasureTheory ProbabilityTheory
open Cslib.MachineLearning.BayesClassifier Cslib.MachineLearning.Bayesian
open scoped ENNReal

/-- Use case: two classes, uniform prior, constant likelihoods. The MAP rule is the MLE rule. -/
example {P : Kernel Bool Bool} [IsFiniteKernel P] [IsMarkovKernel P]
    {π : Measure Bool} [IsFiniteMeasure π]
    {c : ℝ≥0∞} (hμ : ∀ θ, π {θ} = c) (hc : c ≠ 0) (f : Bool → Bool) :
    IsPosteriorArgmax P π f ↔
      ∀ x, (P ∘ₘ π) {x} ≠ 0 → IsMLE P x (f x) := by
  exact isPosteriorArgmax_iff_forall_isMLE_of_uniform hμ hc

/-- Boundary: the uniformity hypothesis is load-bearing. A two-point prior with distinct
masses is not uniform. -/
example (a b : ℝ≥0∞) (h : a ≠ b) :
    ¬ ∀ θ : Bool, ((a • Measure.dirac true + b • Measure.dirac false) : Measure Bool) {θ}
      = a := by
  intro hall
  have hfalse := hall false
  simp at hfalse
  exact h hfalse.symm

/-- Boundary: at a zero-evidence observation the posterior masses vanish, so the pointwise
MAP characterization has nothing to say there. -/
example {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    [Countable Θ] [MeasurableSingletonClass Θ]
    [Countable 𝓧] [MeasurableSingletonClass 𝓧]
    (κ : Kernel Θ 𝓧) (μ : Measure Θ) (x : 𝓧) (h0 : (κ ∘ₘ μ) {x} = 0) (θ : Θ) :
    bayesPosterior κ μ x {θ} = 0 := by
  rw [bayesPosterior_apply κ μ x (measurableSet_singleton θ)]
  have hle : ∫⁻ a in {θ}, κ a {x} ∂μ ≤ (κ ∘ₘ μ) {x} := by
    rw [comp_apply_singleton]
    exact setLIntegral_le_lintegral {θ} _
  rw [h0] at hle
  rw [le_zero_iff.mp hle, mul_zero]

end CSLibExtTest.MachineLearning.Generative.BayesClassifier
