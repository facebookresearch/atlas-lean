/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
public import MathlibExt.Probability.Statistics.ScoreMeanZero

/-!
# Score has mean zero under regularity

For a positive density family differentiable in `θ` everywhere, with differentiation under
the integral justified by a global integrable majorant and probability-law normalization
for every `θ`, the score integrates to zero under `p θ₀ ν`. This supplies the `hs_mean`
hypothesis assumed downstream.

This is the first Bartlett identity; see e.g. Bartlett, M. S. (1953), "Approximate
confidence intervals", Biometrika 40, and Lehmann–Casella, Theory of Point Estimation,
2nd edition.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.ScoreMeanZero

open MeasureTheory Filter Topology

open MathlibExt.Probability.Statistics.MLEAsymptoticNormality

open MathlibExt.Probability.Statistics.FisherInformation

open scoped ENNReal

/-- Fixture A (score unfolding): the logistic-Bernoulli score at `θ` is `1 - σ(θ)` on

`true` and `-σ(θ)` on `false`, where `σ(θ) = (1 + exp(-θ))⁻¹`. Both lambda binders are

typed explicitly. -/

example (θ : ℝ) :

    score (fun (t : ℝ) (_ : Bool) => (1 + Real.exp (-t))⁻¹) θ true =

      1 - (1 + Real.exp (-θ))⁻¹ ∧

    score (fun (t : ℝ) (_ : Bool) => 1 - (1 + Real.exp (-t))⁻¹) θ false =

      -((1 + Real.exp (-θ))⁻¹) := by

  have hvene : (1 : ℝ) + Real.exp (-θ) ≠ 0 := by positivity

  have hvene2 : ((1 : ℝ) + Real.exp (-θ)) ^ 2 ≠ 0 := pow_ne_zero 2 hvene

  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) θ := (hasDerivAt_id (x := θ)).neg

  have hexp : HasDerivAt (fun t => Real.exp (-t)) (Real.exp (-θ) * -1) θ := hneg.exp

  have hadd : HasDerivAt (fun t => 1 + Real.exp (-t)) (Real.exp (-θ) * -1) θ :=

    HasDerivAt.const_add 1 hexp

  have hinv : HasDerivAt (fun t => (1 + Real.exp (-t))⁻¹)

      (-(Real.exp (-θ) * -1) / (1 + Real.exp (-θ)) ^ 2) θ :=

    hadd.inv hvene

  have hinvne : ((1 : ℝ) + Real.exp (-θ))⁻¹ ≠ 0 := inv_ne_zero hvene

  have hlog : HasDerivAt (fun t => Real.log ((1 + Real.exp (-t))⁻¹))

      ((-(Real.exp (-θ) * -1) / (1 + Real.exp (-θ)) ^ 2) / (1 + Real.exp (-θ))⁻¹) θ :=

    hinv.log hinvne

  have h1 : score (fun (t : ℝ) (_ : Bool) => (1 + Real.exp (-t))⁻¹) θ true =

      1 - (1 + Real.exp (-θ))⁻¹ := by

    show deriv (fun t => Real.log ((1 + Real.exp (-t))⁻¹)) θ = 1 - (1 + Real.exp (-θ))⁻¹

    rw [hlog.deriv]

    field_simp

    ring

  have hsub : HasDerivAt (fun t => 1 - (1 + Real.exp (-t))⁻¹)

      (-(-(Real.exp (-θ) * -1) / (1 + Real.exp (-θ)) ^ 2)) θ :=

    HasDerivAt.const_sub 1 hinv

  have hsubne : (1 : ℝ) - (1 + Real.exp (-θ))⁻¹ ≠ 0 := by

    have h1 : (1:ℝ) - (1 + Real.exp (-θ))⁻¹ = Real.exp (-θ) / (1 + Real.exp (-θ)) := by

      field_simp

      ring

    rw [h1]

    positivity

  have hlog2 : HasDerivAt (fun t => Real.log (1 - (1 + Real.exp (-t))⁻¹))

      ((-(-(Real.exp (-θ) * -1) / (1 + Real.exp (-θ)) ^ 2)) / (1 - (1 + Real.exp (-θ))⁻¹)) θ :=

    hsub.log hsubne

  have h2 : score (fun (t : ℝ) (_ : Bool) => 1 - (1 + Real.exp (-t))⁻¹) θ false =

      -((1 + Real.exp (-θ))⁻¹) := by

    show deriv (fun t => Real.log (1 - (1 + Real.exp (-t))⁻¹)) θ = -((1 + Real.exp (-θ))⁻¹)

    rw [hlog2.deriv]

    field_simp

    ring

  exact ⟨h1, h2⟩

/-- Fixture B (through the main theorem): the logistic-Bernoulli score integrates to zero.

The family is globally smooth with `F θ true + F θ false = 1` for every real `θ`, so
`IsProbabilityMeasure` and the constant integrable majorant `1/4` are proved here —
unlike the plain Bernoulli family, which is not normalizable outside `[0,1]`. -/

example (θ₀ : ℝ)

    (F : ℝ → Bool → ℝ)

    (hF : ∀ θ b, F θ b = if b then (1 + Real.exp (-θ))⁻¹ else 1 - (1 + Real.exp (-θ))⁻¹) :

    ∫ x, score F θ₀ x ∂lawOf Measure.count F θ₀ = 0 := by

  have hFtrue : ∀ t, F t true = (1 + Real.exp (-t))⁻¹ := fun t => by simp [hF t true]

  have hFfalse : ∀ t, F t false = 1 - (1 + Real.exp (-t))⁻¹ := fun t => by simp [hF t false]

  have hσnn : ∀ t, (0:ℝ) ≤ (1 + Real.exp (-t))⁻¹ := fun t => by positivity

  have hσ1 : ∀ t, (1 + Real.exp (-t))⁻¹ ≤ 1 := fun t =>
    inv_le_one_of_one_le₀ (by have h := Real.exp_pos (-t); linarith)

  have hderiv_true : ∀ t, HasDerivAt (fun s => F s true)
      (-(Real.exp (-t) * -1) / (1 + Real.exp (-t)) ^ 2) t := by
    intro t
    have hvene : (1:ℝ) + Real.exp (-t) ≠ 0 := by positivity
    have hFeq : (fun s => F s true) = (fun s => (1 + Real.exp (-s))⁻¹) :=
      funext fun s => by simp [hF s true]
    rw [hFeq]
    exact ((HasDerivAt.const_add 1 ((hasDerivAt_id (x := t)).neg.exp)).inv hvene)

  have hderiv_false : ∀ t, HasDerivAt (fun s => F s false)
      (-(-(Real.exp (-t) * -1) / (1 + Real.exp (-t)) ^ 2)) t := by
    intro t
    have hvene : (1:ℝ) + Real.exp (-t) ≠ 0 := by positivity
    have hFeq : (fun s => F s false) = (fun s => 1 - (1 + Real.exp (-s))⁻¹) :=
      funext fun s => by simp [hF s false]
    rw [hFeq]
    exact HasDerivAt.const_sub 1
      (((HasDerivAt.const_add 1 ((hasDerivAt_id (x := t)).neg.exp)).inv hvene))

  have hderiv_true_eq : ∀ t, deriv (fun s => F s true) t
      = Real.exp (-t) / (1 + Real.exp (-t)) ^ 2 := fun t => by
    rw [(hderiv_true t).deriv]; ring

  have hderiv_false_eq : ∀ t, deriv (fun s => F s false) t
      = -(Real.exp (-t) / (1 + Real.exp (-t)) ^ 2) := fun t => by
    rw [(hderiv_false t).deriv]; ring

  have hle : ∀ t : ℝ, Real.exp (-t) / (1 + Real.exp (-t)) ^ 2 ≤ 1 / 4 := by
    intro t
    have hden : (0:ℝ) < (1 + Real.exp (-t)) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (1 - Real.exp (-t)), Real.exp_pos (-t)]

  have hnn : ∀ t : ℝ, (0:ℝ) ≤ Real.exp (-t) / (1 + Real.exp (-t)) ^ 2 := by
    intro t
    positivity

  have hprob : ∀ θ, IsProbabilityMeasure (lawOf Measure.count F θ) := by
    intro θ
    refine ⟨?_⟩
    show lawOf Measure.count F θ Set.univ = 1
    rw [lawOf, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_count, tsum_bool, hFfalse θ, hFtrue θ,
      ← ENNReal.ofReal_add (by linarith [hσnn θ, hσ1 θ]) (hσnn θ),
      sub_add_cancel, ENNReal.ofReal_one]

  have hbound : ∃ C : Bool → ℝ, Integrable C Measure.count ∧
      ∀ x, ∀ t, ‖deriv (fun s => F s x) t‖ ≤ C x := by
    refine ⟨fun _ => 1 / 4, integrable_const _, fun x t => ?_⟩
    cases x with
    | false =>
      rw [hderiv_false_eq t, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hnn t)]
      exact hle t
    | true =>
      rw [hderiv_true_eq t, Real.norm_eq_abs, abs_of_nonneg (hnn t)]
      exact hle t

  have hpos : ∀ x, 0 < F θ₀ x := by

    intro x

    cases x

    case false =>

      rw [hFfalse]

      have h1 : (1:ℝ) - (1 + Real.exp (-θ₀))⁻¹

          = Real.exp (-θ₀) / (1 + Real.exp (-θ₀)) := by

        have hvene : (1:ℝ) + Real.exp (-θ₀) ≠ 0 := by positivity

        field_simp

        ring

      rw [h1]

      positivity

    case true =>

      rw [hFtrue]

      positivity

  have hmeas : ∀ θ, Measurable (F θ) := fun θ => measurable_of_countable _

  have hdiff : ∀ x, ∀ θ, DifferentiableAt ℝ (fun t => F t x) θ := by

    intro x θ

    cases x

    case false =>

      have hFeq : (fun t => F t false) = (fun t => 1 - (1 + Real.exp (-t))⁻¹) :=

        funext fun t => by simp [hF t false]

      rw [hFeq]

      have hvene : (1:ℝ) + Real.exp (-θ) ≠ 0 := by positivity

      exact (HasDerivAt.const_sub 1 ((HasDerivAt.const_add 1

        ((hasDerivAt_id (x := θ)).neg.exp)).inv hvene)).differentiableAt

    case true =>

      have hFeq : (fun t => F t true) = (fun t => (1 + Real.exp (-t))⁻¹) :=

        funext fun t => by simp [hF t true]

      rw [hFeq]

      have hvene : (1:ℝ) + Real.exp (-θ) ≠ 0 := by positivity

      exact ((HasDerivAt.const_add 1 ((hasDerivAt_id (x := θ)).neg.exp)).inv

        hvene).differentiableAt

  exact integral_score_mean_zero hpos hmeas hdiff hprob hbound

/-- Fixture C (boundary): with support depending on `θ`, differentiability in `θ` fails at

the boundary point — the global differentiability hypothesis visibly fails there. -/

example (x : ℝ) (hx : 0 < x) :

    ¬ DifferentiableAt ℝ (fun (t : ℝ) => (if 0 ≤ x ∧ x ≤ t then (1 / t : ℝ) else 0)) x := by

  intro hdiff

  have hcont := hdiff.continuousAt

  have hval : (if 0 ≤ x ∧ x ≤ x then (1 / x : ℝ) else 0) = 1 / x := by

    have hcond : 0 ≤ x ∧ x ≤ x := ⟨hx.le, le_rfl⟩

    simp [hcond]

  have hseq : Tendsto (fun n : ℕ => x - 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by

    have h : Tendsto (fun n : ℕ => x - 1 / ((n : ℝ) + 1)) atTop (𝓝 (x - 0)) :=

      tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

    simpa using h

  have hlim := hcont.tendsto.comp hseq

  rw [hval] at hlim

  have hconst : ((fun (t : ℝ) => (if 0 ≤ x ∧ x ≤ t then (1 / t : ℝ) else 0)) ∘

      (fun n : ℕ => x - 1 / ((n : ℝ) + 1))) = fun _ => (0:ℝ) := by

    funext n

    simp only [Function.comp_apply]

    have hneg : ¬ (0 ≤ x ∧ x ≤ x - 1 / ((n:ℝ) + 1)) := by

      intro hcon

      have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity

      linarith [hcon.2]

    simp only [hneg, ite_false]

  rw [hconst] at hlim

  have heq := tendsto_nhds_unique hlim tendsto_const_nhds

  have hposx : (0:ℝ) < 1 / x := by positivity

  linarith

end MathlibExtTest.Probability.Statistics.ScoreMeanZero
