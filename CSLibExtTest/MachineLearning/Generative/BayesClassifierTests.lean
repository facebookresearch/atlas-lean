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
