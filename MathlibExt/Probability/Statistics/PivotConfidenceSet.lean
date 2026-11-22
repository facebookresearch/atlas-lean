/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Quantile
public import MathlibExt.Probability.CdfContinuityPoints
public import MathlibExt.Probability.Statistics.ConfidenceSet
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pivot confidence-set coverage

A pivot `T` with a continuous reference law `ν` (the same law under every
`P θ`) yields a confidence set from the `α / 2` and `1 - α / 2`
quantiles of `ν`, with coverage at least `1 - α`. The key step is that
under a continuous cdf the cdf at the generalized-inverse quantile is
exactly the level (`ProbabilityTheory.cdf_cdfQuantile_eq_of_continuous`);
each tail then has probability at most `α / 2` (Atlas roadmap ST02.T03).

The parameter type `Θ` carries no order and `T x θ` is arbitrary, so the
confidence set need not be an interval. In a location model, `T x θ = x - θ`,
it is the interval `[x - q_{1 - α/2}, x - q_{α/2}]`.
-/

@[expose] public section

open MeasureTheory Set Topology

namespace MathlibExt.Probability.Statistics.PivotConfidenceSet

open MeasureTheory ProbabilityTheory

/-- The pivot confidence set for an estimand `θ` from observation `x`:
the set of `θ` whose pivot value `T x θ` lies between the `α/2` and
`1 - α/2` quantiles of the reference law `ν`. It need not be an interval. -/
noncomputable def pivotConfidenceSet {X Θ : Type*} (T : X → Θ → ℝ) (ν : Measure ℝ)
    (α : ℝ) (x : X) : Set Θ :=
  {θ | cdfQuantile ν (α / 2) ≤ T x θ ∧ T x θ ≤ cdfQuantile ν (1 - α / 2)}

/-- **Pivot confidence-set coverage (ST02.T03).** If `T x θ` has the
continuous reference law `ν` under `P θ` for every `θ`, then the pivot
confidence set has coverage at least `1 - α`: each tail probability is at
most `α / 2` (via `cdf_cdfQuantile_eq_of_continuous` and the cdf), and the
non-coverage event is contained in their union. -/
theorem pivotConfidenceSet_coverage {X Θ : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (T : X → Θ → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcont : Continuous (cdf ν))
    (hlaw : ∀ θ, HasLaw (fun x => T x θ) ν (P θ))
    (hmeas : ∀ θ, Measurable fun x => T x θ)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (θ : Θ) :
    1 - α ≤ (P θ).real {x | θ ∈ pivotConfidenceSet T ν α x} := by
  have hα2 : α / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have h1α2 : 1 - α / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hqlo_eq : cdf ν (cdfQuantile ν (α / 2)) = α / 2 :=
    cdf_cdfQuantile_eq_of_continuous ν hcont hα2
  have hqhi_eq : cdf ν (cdfQuantile ν (1 - α / 2)) = 1 - α / 2 :=
    cdf_cdfQuantile_eq_of_continuous ν hcont h1α2
  have htail1 : (P θ).real {x | T x θ < cdfQuantile ν (α / 2)} ≤ α / 2 := by
    have hmap : (P θ).real {x | T x θ < cdfQuantile ν (α / 2)}
        = ν.real (Set.Iio (cdfQuantile ν (α / 2))) := by
      have h : (P θ).real {x | T x θ < cdfQuantile ν (α / 2)}
          = ν.real (Set.Iio (cdfQuantile ν (α / 2))) :=
        (hlaw θ).measureReal_eq measurableSet_Iio
      simpa using h
    rw [hmap]
    calc ν.real (Set.Iio (cdfQuantile ν (α / 2)))
        ≤ ν.real (Set.Iic (cdfQuantile ν (α / 2))) :=
          measureReal_mono Set.Iio_subset_Iic_self
      _ = α / 2 := by rw [← cdf_eq_real ν _, hqlo_eq]
  have htail2 : (P θ).real {x | cdfQuantile ν (1 - α / 2) < T x θ} ≤ α / 2 :=
    measureReal_lt_le_of_le_cdf (hlaw θ) hqhi_eq.ge
  have hsub : {x | θ ∈ pivotConfidenceSet T ν α x}ᶜ
      ⊆ {x | T x θ < cdfQuantile ν (α / 2)}
        ∪ {x | cdfQuantile ν (1 - α / 2) < T x θ} := by
    intro x hx
    have hx' : ¬ (cdfQuantile ν (α / 2) ≤ T x θ ∧ T x θ ≤ cdfQuantile ν (1 - α / 2)) := by
      simpa [pivotConfidenceSet] using hx
    rw [not_and_or] at hx'
    have hgoal : T x θ < cdfQuantile ν (α / 2) ∨ cdfQuantile ν (1 - α / 2) < T x θ :=
      hx'.elim (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
    simpa using hgoal
  have hnoncov : (P θ).real {x | θ ∈ pivotConfidenceSet T ν α x}ᶜ ≤ α := by
    calc (P θ).real {x | θ ∈ pivotConfidenceSet T ν α x}ᶜ
        ≤ (P θ).real ({x | T x θ < cdfQuantile ν (α / 2)}
            ∪ {x | cdfQuantile ν (1 - α / 2) < T x θ}) :=
          measureReal_mono hsub
      _ ≤ (P θ).real {x | T x θ < cdfQuantile ν (α / 2)}
            + (P θ).real {x | cdfQuantile ν (1 - α / 2) < T x θ} :=
          measureReal_union_le _ _
      _ ≤ α / 2 + α / 2 := add_le_add htail1 htail2
      _ = α := by ring
  have hmeas_cov : MeasurableSet {x | θ ∈ pivotConfidenceSet T ν α x} := by
    have heq : {x | θ ∈ pivotConfidenceSet T ν α x}
        = (fun x => T x θ) ⁻¹' (Set.Icc (cdfQuantile ν (α / 2))
          (cdfQuantile ν (1 - α / 2))) := by
      ext x
      simp [pivotConfidenceSet]
    rw [heq]
    exact (hmeas θ) measurableSet_Icc
  have hcov := probReal_compl_eq_one_sub (μ := P θ)
    (s := {x | θ ∈ pivotConfidenceSet T ν α x}) hmeas_cov
  linarith

end MathlibExt.Probability.Statistics.PivotConfidenceSet
