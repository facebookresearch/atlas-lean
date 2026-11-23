/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Bayesian.FiniteConsistency
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for finite-model posterior consistency
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Bayesian.FiniteConsistency

open MeasureTheory ProbabilityTheory Filter Topology MathlibExt.Probability.Statistics.Bayesian

/-- Two-point likelihood on `Bool`: the observation equals `θ` with probability `2/3`. -/
private noncomputable def bitLik (θ x : Bool) : ℝ := if x = θ then 2 / 3 else 1 / 3

/-- The law of one observation under `θ₀ = true` is a probability measure. -/
private instance : IsProbabilityMeasure (weightLaw (bitLik true)) := by
  exact isProbabilityMeasure_weightLaw _ (fun x => by unfold bitLik; split_ifs <;> norm_num)
    (by simp only [Fintype.sum_bool, bitLik]; norm_num)

/-- Prior zero at the truth: the posterior weight of `θ₀` is `0` for every `n`, so consistency
fails without `0 < π θ₀`. -/
example {Θ 𝓧 Ω : Type*} [Fintype Θ] (π : Θ → ℝ) (f : Θ → 𝓧 → ℝ) (X : ℕ → Ω → 𝓧) (θ₀ : Θ)
    (hπ₀ : π θ₀ = 0) (n : ℕ) (ω : Ω) :
    postWeight π f X n ω θ₀ = 0 := by
  simp [postWeight, hπ₀]

/-- Identical laws preserve prior odds: with `f θ₁ = f θ₀` (no KL separation) the posterior odds
of `θ₁` against `θ₀` equal the prior odds for every `n`. -/
example {Θ 𝓧 Ω : Type*} [Fintype Θ] (π : Θ → ℝ) (f : Θ → 𝓧 → ℝ) (X : ℕ → Ω → 𝓧)
    (θ₀ θ₁ : Θ) (hf : f θ₁ = f θ₀) (n : ℕ) (ω : Ω) :
    postWeight π f X n ω θ₁ * π θ₀ = postWeight π f X n ω θ₀ * π θ₁ := by
  simp only [postWeight, hf]
  ring

/-- One-point model: the posterior weight is identically `1`. -/
example {𝓧 Ω : Type*} (π : Unit → ℝ) (hπ : 0 < π ()) (f : Unit → 𝓧 → ℝ)
    (hf_pos : ∀ θ x, 0 < f θ x) (X : ℕ → Ω → 𝓧) (n : ℕ) (ω : Ω) :
    postWeight π f X n ω () = 1 := by
  rw [postWeight, Fintype.sum_unique]
  exact div_self (mul_pos hπ (Finset.prod_pos fun i _ => hf_pos () (X i ω))).ne'

/-- KL separation holds in the two-point model (`KL = (1/3) log 2`). -/
example : ∀ θ : Bool, θ ≠ true →
    0 < ∑ x, bitLik true x * Real.log (bitLik true x / bitLik θ x) := by
  intro θ hθ
  obtain rfl : θ = false := by simpa using hθ
  simp only [Fintype.sum_bool, bitLik]
  norm_num
  rw [one_div (2 : ℝ), Real.log_inv]
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- Every hypothesis realized: i.i.d. coordinates under the infinite product of the `θ₀ = true`
law, uniform prior. Derive this from `ae_tendsto_postWeight_one`. -/
example : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => weightLaw (bitLik true)),
    Tendsto (fun n => postWeight (fun _ : Bool => (1 / 2 : ℝ)) bitLik
      (fun i (ω : ℕ → Bool) => ω i) n ω true) atTop (𝓝 1) := by
  refine ae_tendsto_postWeight_one (fun _ : Bool => (1 / 2 : ℝ)) (fun _ => by norm_num) true
    (by norm_num) bitLik (fun θ x => by unfold bitLik; split_ifs <;> norm_num)
    (fun θ => by cases θ <;> simp only [Fintype.sum_bool, bitLik] <;> norm_num) ?_
    (fun i (ω : ℕ → Bool) => ω i) (fun i => measurable_pi_apply i)
    (fun i => Measure.infinitePi_map_eval _ i) ?_
  · intro θ hθ
    obtain rfl : θ = false := by simpa using hθ
    simp only [Fintype.sum_bool, bitLik]
    norm_num
    rw [one_div (2 : ℝ), Real.log_inv]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  · intro i j hij
    exact (iIndepFun_infinitePi (P := fun _ : ℕ => weightLaw (bitLik true))
      (X := fun _ : ℕ => (id : Bool → Bool)) (fun _ => measurable_id)).indepFun hij

end MathlibExtTest.Probability.Statistics.Bayesian.FiniteConsistency

#print axioms MathlibExt.Probability.Statistics.Bayesian.ae_tendsto_postWeight_one
#print axioms MathlibExt.Probability.Statistics.Bayesian.isProbabilityMeasure_weightLaw

namespace MathlibExtTest.Probability.Statistics.Bayesian.FiniteConsistency

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Statistics.Bayesian

/-- Use case: truth `1 / 2` against alternative `3 / 4` with unit prior weights. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin 2) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = weightLaw (bernPMF (1 / 2)))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => postWeight (fun _ : Fin 2 => (1 : ℝ))
        (fun θ : Fin 2 => bernPMF (if θ = 0 then (1 / 2 : ℝ) else 3 / 4)) X n ω (0 : Fin 2))
      atTop (𝓝 1) := by
  exact twoPoint_postWeight_tendsto_one (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) X hX hlaw hindep

/-- Boundary: identical laws have zero self-KL, so the separation hypothesis excludes them. -/
example : ¬ 0 < ∑ x : Fin 2,
    bernPMF (1 / 2) x * Real.log (bernPMF (1 / 2) x / bernPMF (1 / 2) x) := by
  have hpos : ∀ x : Fin 2, 0 < bernPMF (1 / 2 : ℝ) x := fun x => by
    unfold bernPMF
    split <;> norm_num
  have h : ∑ x : Fin 2, bernPMF (1 / 2) x * Real.log (bernPMF (1 / 2) x / bernPMF (1 / 2) x)
      = 0 := by
    rw [Fin.sum_univ_two]
    have h0 : bernPMF (1 / 2 : ℝ) 0
        * Real.log (bernPMF (1 / 2 : ℝ) 0 / bernPMF (1 / 2 : ℝ) 0) = 0 := by
      rw [div_self (ne_of_gt (hpos 0)), Real.log_one, mul_zero]
    have h1 : bernPMF (1 / 2 : ℝ) 1
        * Real.log (bernPMF (1 / 2 : ℝ) 1 / bernPMF (1 / 2 : ℝ) 1) = 0 := by
      rw [div_self (ne_of_gt (hpos 1)), Real.log_one, mul_zero]
    rw [h0, h1, add_zero]
  rw [h]
  exact lt_irrefl 0

/-- Degenerate case: with no observations the posterior weight is the prior ratio. -/
example {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → Fin 2) (ω : Ω)
    (f : Fin 2 → Fin 2 → ℝ) :
    postWeight (fun _ : Fin 2 => (1 : ℝ)) f X 0 ω (0 : Fin 2) = 1 / 2 := by
  simp only [postWeight, Finset.range_zero, Finset.prod_empty, mul_one]
  rw [Fin.sum_univ_two]
  norm_num

end MathlibExtTest.Probability.Statistics.Bayesian.FiniteConsistency
