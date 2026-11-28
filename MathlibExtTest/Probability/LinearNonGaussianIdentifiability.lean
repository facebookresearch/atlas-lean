/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.LinearNonGaussianIdentifiability
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Tests for linear non-Gaussian identifiability

Two independent fair coin tosses admit no backward coefficient at any nonzero forward slope.
-/

open MeasureTheory ProbabilityTheory
open MathlibExt.ComputerScience.LinearNonGaussianIdentifiabilityWanted

namespace MathlibExtTest.Probability.LinearNonGaussianIdentifiability

private noncomputable abbrev coin : Measure ℝ :=
  bernoulliMeasure 0 1 ⟨1 / 2, by norm_num, by norm_num⟩

private lemma coin_zero : coin.real {0} = 1 / 2 := by
  classical
  norm_num [coin, bernoulliMeasure_real_apply _ (measurableSet_singleton _),
    unitInterval.toNNReal]
  rfl

private lemma nonconstant {Z : ℝ × ℝ → ℝ} (hZ : (coin.prod coin).map Z = coin) (c : ℝ) :
    ¬ Z =ᵐ[coin.prod coin] fun _ => c := by
  intro h
  have hdirac : coin = Measure.dirac c := by
    rw [← hZ, Measure.map_congr h, Measure.map_const]
    simp
  have hm := coin_zero
  rw [hdirac] at hm
  by_cases hc : c = 0 <;> simp [Measure.real, hc] at hm

example {φ : ℝ} (hφ : φ ≠ 0) :
    ¬ ∃ ψ : ℝ, IndepFun (fun p : ℝ × ℝ => p.1 - ψ * (φ * p.1 + p.2))
      (fun p => φ * p.1 + p.2) (coin.prod coin) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨⟨m, v, hv, hlaw⟩, _⟩ := gaussian_of_indepFun_backward
    measurable_fst measurable_snd (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)
    (nonconstant (by simp)) (nonconstant (by simp)) hφ hψ
  have := nullSingletonClass_gaussianReal (μ := m) hv
  have hcoin : coin = gaussianReal m v := by simpa using hlaw
  have hm := coin_zero
  rw [hcoin] at hm
  norm_num [Measure.real] at hm

end MathlibExtTest.Probability.LinearNonGaussianIdentifiability
