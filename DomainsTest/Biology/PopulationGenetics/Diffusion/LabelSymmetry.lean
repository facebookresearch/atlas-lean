/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.LabelSymmetry
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Probability.Process.Filtration

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.LabelSymmetry

open MathlibExt.Biology.PopulationGenetics.Diffusion
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
open MeasureTheory
open scoped NNReal

/-- Neutral generator conjugation at `y = 1 / 2` for the quadratic test function. -/
example : generator (-0) (fun z : ℝ => z ^ 2) (1 - 1 / 2)
    = generator 0 (fun z : ℝ => (1 - z) ^ 2) (1 / 2) :=
  generator_neg_one_sub 0 (fun z : ℝ => z ^ 2) (1 / 2)

/-- Endpoint reading: conjugation at `σ = 2`, `y = 0`, as the identity instance. -/
example : generator (-2) (fun z : ℝ => z ^ 2) (1 - 0)
    = generator 2 (fun z : ℝ => (1 - z) ^ 2) 0 :=
  generator_neg_one_sub 2 (fun z : ℝ => z ^ 2) 0

/-- Reflection preserves the absorption time, read pointwise. -/
example {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    absorptionTime (fun t ω => 1 - X t ω) ω = absorptionTime X ω :=
  congrFun absorptionTime_one_sub ω

/-- Neutral loss reading: loss probability of a neutral solution started at `x`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ} {x : ℝ}
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 0} = 1 - kimuraFixation 0 x :=
  measureReal_loss hX hX0

/-- Neutral reflection preserves the solution predicate, as a term. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X) :
    IsWrightFisherSolution (-0) ℱ μ (fun t ω => 1 - X t ω) :=
  IsWrightFisherSolution.one_sub hX

#print axioms generator_neg_one_sub
#print axioms IsWrightFisherSolution.one_sub
#print axioms absorptionTime_one_sub
#print axioms measureReal_loss

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.LabelSymmetry
