/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Horvitz-Thompson total estimator for finite populations

Finite-population sampling with a normalized `PMF` on samples: inclusion
probabilities derived from the design, the Horvitz-Thompson total, and its
unbiasedness for the population total and mean.

## References

- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without
  replacement from a finite universe", Journal of the American Statistical
  Association 47(260) (1952), 663-685.
-/

@[expose] public section

namespace MathlibExt.Probability.Sampling

open MeasureTheory

/-- Inclusion probability of unit `i`: total mass of samples containing `i`. -/
noncomputable def inclusionProbability {α : Type*} [Fintype α] [DecidableEq α]
    (p : PMF (Finset α)) (i : α) : ℝ :=
  ∑ s, if i ∈ s then (p s).toReal else 0

/-- Horvitz-Thompson total estimator at sample `s`: `∑ i ∈ s, y i / π i`. -/
noncomputable def horvitzThompsonTotal {α : Type*} [Fintype α] [DecidableEq α]
    (p : PMF (Finset α)) (y : α → ℝ) (s : Finset α) : ℝ :=
  ∑ i ∈ s, y i / inclusionProbability p i

/-- The Horvitz-Thompson total is unbiased for the population total
    (Horvitz and Thompson (1952)). -/
theorem integral_horvitzThompsonTotal {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]
    (p : PMF (Finset α)) (y : α → ℝ)
    (hpos : ∀ i, 0 < inclusionProbability p i) :
    ∫ s, horvitzThompsonTotal p y s ∂p.toMeasure = ∑ i, y i := by
  have hexpand : ∀ s : Finset α, (p s).toReal * horvitzThompsonTotal p y s
      = ∑ i, if i ∈ s then (p s).toReal * (y i / inclusionProbability p i)
        else 0 := by
    intro s
    unfold horvitzThompsonTotal
    rw [Finset.mul_sum, ← Finset.sum_ite_mem_eq]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hπ : inclusionProbability p i ≠ 0 := ne_of_gt (hpos i)
  calc ∑ s, (if i ∈ s then (p s).toReal * (y i / inclusionProbability p i)
        else 0)
      = ∑ s, (y i / inclusionProbability p i)
        * (if i ∈ s then (p s).toReal else 0) := by
        congr with s
        by_cases h : i ∈ s <;> simp [h, mul_comm]
    _ = (y i / inclusionProbability p i)
        * ∑ s, (if i ∈ s then (p s).toReal else 0) := by
        rw [Finset.mul_sum]
    _ = (y i / inclusionProbability p i) * inclusionProbability p i := rfl
    _ = y i := div_mul_cancel₀ _ hπ

/-- The Horvitz-Thompson mean is unbiased for the population mean.
    The identity also holds at cardinality zero under Lean's division
    convention. -/
theorem integral_horvitzThompsonTotal_div_card {α : Type*} [Fintype α]
    [DecidableEq α] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)] (p : PMF (Finset α)) (y : α → ℝ)
    (hpos : ∀ i, 0 < inclusionProbability p i) (_hcard : 0 < Fintype.card α) :
    ∫ s, (horvitzThompsonTotal p y s / (Fintype.card α : ℝ)) ∂p.toMeasure
      = (∑ i, y i) / (Fintype.card α : ℝ) := by
  rw [MeasureTheory.integral_div, integral_horvitzThompsonTotal p y hpos]

end MathlibExt.Probability.Sampling
