/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Data.Matrix.Mul

/-!
# Ordinary kriging is unbiased

The ordinary kriging estimator is a weighted sum of observations whose
weights solve the ordinary kriging system. That system is the covariance
equations together with the unbiasedness constraint that the weights sum
to `1`. If every observation has the same mean, the estimator has that
mean: unbiasedness follows from the constraint alone, while the
covariance equations pin down which weights solve the system.

## i. Overview

For a finite set of sites, weights `lam`, and observations `Z i` each with
mean `mean`, the kriging estimator `∑ i, lam i * Z i` has mean `mean`
whenever `lam` satisfies the ordinary kriging system. Weights summing to
`0.6` would give mean `0.6 * mean`, so the sum-to-one constraint is
needed.

## ii. Key results

- `EarthScience.ordinary_kriging_unbiased`: the kriging estimator has
  mean `mean` under the ordinary kriging system.

## iii. Table of contents

- A. Unbiasedness

## iv. References

- `MeasureTheory.integral_finsetSum`, `MeasureTheory.integral_const_mul`
  in Mathlib.

## A. Unbiasedness
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace EarthScience

/-- Ordinary kriging is unbiased: the kriging weights solve the ordinary
kriging system, whose last equation is the unbiasedness constraint that the
weights sum to `1`. If every observation has the same mean `mean`, the
kriging estimator `∑ i, lam i * Z i` has mean `mean`. The covariance
equations pin down which weights solve the system; unbiasedness itself
follows from the constraint. -/
theorem ordinary_kriging_unbiased {ι : Type*} [Fintype ι] {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ι → ℝ} {mean : ℝ}
    (hMean : ∀ i, ∫ ω, Z ω i ∂μ = mean)
    (hInt : ∀ i, Integrable (fun ω => Z ω i) μ)
    {C : Matrix ι ι ℝ} {c : ι → ℝ} {m : ℝ} {lam : ι → ℝ}
    (hSys : (∀ i, (C *ᵥ lam) i + m = c i) ∧ ∑ i, lam i = 1) :
    ∫ ω, ∑ i, lam i * Z ω i ∂μ = mean := by
  have h1 : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun ω => lam i * Z ω i) μ :=
    fun i _ => (hInt i).const_mul (lam i)
  rw [integral_finsetSum _ h1]
  simp_rw [integral_const_mul, hMean]
  rw [← Finset.sum_mul, hSys.2, one_mul]

end EarthScience
