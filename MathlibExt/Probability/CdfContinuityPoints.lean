/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.CDF
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Continuity points of the cumulative distribution function

For a probability measure `μ` on `ℝ`, the cumulative distribution function
`cdf μ` is continuous at `x` exactly when `μ` has no atom at `x`, the mass of
a half-open interval is the corresponding increment of the cdf, and the
continuity points of the cdf form a dense subset of `ℝ`.

## Source

This formalizes the cdf lemmas of
`v1/Atlas/TheoryOfProbability/code/Portmanteau.lean`:
`cdf_continuousAt_singleton_null`, `cdf_continuousAt_frontier_Iic_null`,
`probMeasure_Ioc_eq_toNNReal_cdf`, and `dense_cdf_continuityPoints`, plus a
new converse: `continuousAt_cdf_iff_measure_singleton_eq_zero`, which
characterizes continuity of the cdf at a point by the absence of an atom
there. The forward direction is the v1 lemma; the converse follows from
the atom-jump formula `measure_singleton_eq_cdf_sub_leftLim` below, which
is not in v1. The `Portmanteau` theorem itself (`weakConvergence_iff_bounded_continuous`
in v1) is Mathlib's `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`
and is not claimed here.

## Main results

* `MathlibExt.Probability.CdfContinuityPoints.measure_singleton_eq_cdf_sub_leftLim`:
  the atom `μ {x}` is the jump `cdf μ x - leftLim (cdf μ) x` of the cdf.
* `MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero`:
  `cdf μ` is continuous at `x` iff `μ {x} = 0`.
* `MathlibExt.Probability.CdfContinuityPoints.cdf_continuousAt_singleton_null`:
  continuity of the cdf at `x` implies `μ {x} = 0`.
* `MathlibExt.Probability.CdfContinuityPoints.cdf_continuousAt_frontier_Iic_null`:
  continuity of the cdf at `x` implies `μ (frontier (Iic x)) = 0`.
* `MathlibExt.Probability.CdfContinuityPoints.measure_Ioc_eq_ofReal_cdf`:
  `μ (Ioc a b) = ENNReal.ofReal (cdf μ b - cdf μ a)`.
* `MathlibExt.Probability.CdfContinuityPoints.dense_cdf_continuityPoints`:
  the continuity points of `cdf μ` are dense in `ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace MathlibExt.Probability.CdfContinuityPoints

/-- The atom of a probability measure at `x` is the jump of its cdf at `x`:
`μ {x} = ENNReal.ofReal (cdf μ x - leftLim (cdf μ) x)`. -/
theorem measure_singleton_eq_cdf_sub_leftLim
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    μ {x} = ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) := by
  have h := StieltjesFunction.measure_singleton (cdf μ) x
  rwa [measure_cdf] at h

/-- The cdf of a probability measure is continuous at `x` if and only if the
measure has no atom at `x`. -/
theorem continuousAt_cdf_iff_measure_singleton_eq_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ContinuousAt (cdf μ) x ↔ μ {x} = 0 := by
  constructor
  · intro hx
    rw [measure_singleton_eq_cdf_sub_leftLim μ x]
    have hlim : Function.leftLim (cdf μ) x = cdf μ x := by
      have h := (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mp hx
      rw [StieltjesFunction.rightLim_eq] at h
      exact h
    rw [hlim, sub_self, ENNReal.ofReal_zero]
  · intro hx
    have hle : Function.leftLim (cdf μ) x ≤ cdf μ x :=
      (monotone_cdf μ).leftLim_le le_rfl
    have hsub : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 := by
      have h := measure_singleton_eq_cdf_sub_leftLim μ x
      rw [hx] at h
      exact ENNReal.ofReal_eq_zero.mp h.symm
    have heq : Function.leftLim (cdf μ) x = cdf μ x := by linarith
    have hlim : Function.leftLim (cdf μ) x = Function.rightLim (cdf μ) x := by
      rw [heq, StieltjesFunction.rightLim_eq]
    exact (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr hlim

/-- If the cdf of a probability measure `μ` is continuous at `x`, then `μ`
assigns zero mass to the singleton `{x}`. Continuity of the cdf at `x`
corresponds to absence of an atom at `x`. -/
theorem cdf_continuousAt_singleton_null
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) (hx : ContinuousAt (cdf μ) x) :
    μ {x} = 0 :=
  (continuousAt_cdf_iff_measure_singleton_eq_zero μ x).mp hx

/-- If the cdf of a probability measure `μ` is continuous at `x`, then the
boundary `frontier (Iic x) = {x}` is `μ`-null. -/
theorem cdf_continuousAt_frontier_Iic_null
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) (hx : ContinuousAt (cdf μ) x) :
    μ (frontier (Iic x)) = 0 := by
  rw [frontier_Iic]
  exact cdf_continuousAt_singleton_null μ x hx

/-- For a probability measure `μ` on `ℝ`, the mass of a half-open interval
`(a, b]` equals `ENNReal.ofReal (cdf μ b - cdf μ a)`. -/
theorem measure_Ioc_eq_ofReal_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ) :
    μ (Ioc a b) = ENNReal.ofReal (cdf μ b - cdf μ a) := by
  have h := StieltjesFunction.measure_Ioc (cdf μ) a b
  rwa [measure_cdf] at h

/-- The set of continuity points of the cdf of a probability measure is dense
in `ℝ`. This follows from the fact that a monotone function has only
countably many discontinuities. -/
theorem dense_cdf_continuityPoints (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Dense {x : ℝ | ContinuousAt (cdf μ) x} := by
  have hcount : {x : ℝ | ¬ContinuousAt (cdf μ) x}.Countable :=
    (monotone_cdf μ).countable_not_continuousAt
  have hd := hcount.dense_compl (𝕜 := ℝ)
  refine hd.mono ?_
  intro x hx
  exact not_not.mp hx

end MathlibExt.Probability.CdfContinuityPoints
