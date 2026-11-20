/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Sensitivity and uncertainty propagation: covariance of a linear map

For a random vector `X` with finite second moments and a deterministic
linear map `J`, `Cov(JX) = J Cov(X) Jᵀ`.

## i. Overview

Entrywise, `Cov(JX) i j = ∑ a, ∑ b, J i a * J j b * Cov(X) a b`,
which is the `(i, j)` entry of `J * Cov(X) * Jᵀ`. The proof unfolds
`mulVec` into finite sums and uses bilinearity of covariance
(`covariance_fun_sum_fun_sum`, `covariance_const_mul_left/right`).
Covariance carries squared units; cross-covariances are retained, not
dropped. The nonlinear delta method is out of scope: it needs a
separately bounded Taylor remainder.

## ii. Key results

- `EarthScience.covariance_linear_map`: `Cov(JX) = J Cov(X) Jᵀ`,
  entrywise.
- `EarthScience.variance_linear_combination`: the variance of one
  linear combination is the quadratic form in the covariance matrix.

## iii. Table of contents

- A. Covariance of a linear map
- B. Variance of a linear combination

## iv. References

- `ProbabilityTheory.covariance_fun_sum_fun_sum`,
  `ProbabilityTheory.variance_fun_sum`,
  `ProbabilityTheory.covariance_const_mul_left/right` (Mathlib).

## A. Covariance of a linear map
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace EarthScience

/-- Covariance of a deterministic linear map, entrywise:
`Cov(JX) i j = ∑ a, ∑ b, J i a * J j b * Cov(X) a b`.
The right side is the `(i, j)` entry of `J * Cov(X) * Jᵀ`;
covariance carries squared units and cross-covariances are retained. -/
theorem covariance_linear_map {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m p : ℕ} {X : Ω → Fin m → ℝ} {J : Matrix (Fin p) (Fin m) ℝ}
    (hLp : ∀ a, MemLp (fun ω => X ω a) 2 μ) :
    ∀ i j, covariance (fun ω => Matrix.mulVec J (X ω) i)
        (fun ω => Matrix.mulVec J (X ω) j) μ
      = ∑ a, ∑ b, J i a * J j b
          * covariance (fun ω => X ω a) (fun ω => X ω b) μ := by
  intro i j
  have hmul : ∀ (k : Fin p) (ω : Ω), Matrix.mulVec J (X ω) k = ∑ a, J k a * X ω a := by
    intro k ω
    simp [Matrix.mulVec, dotProduct]
  have e1 : (fun ω => Matrix.mulVec J (X ω) i) = fun ω => ∑ a, J i a * X ω a :=
    funext (hmul i)
  have e2 : (fun ω => Matrix.mulVec J (X ω) j) = fun ω => ∑ a, J j a * X ω a :=
    funext (hmul j)
  have hX : ∀ a, MemLp (fun ω => J i a * X ω a) 2 μ := fun a => (hLp a).const_mul _
  have hY : ∀ b, MemLp (fun ω => J j b * X ω b) 2 μ := fun b => (hLp b).const_mul _
  rw [e1, e2, covariance_fun_sum_fun_sum hX hY]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-! ## B. Variance of a linear combination -/

/-- Diagonal case: the variance of one linear combination is the
quadratic form in the covariance matrix. -/
theorem variance_linear_combination {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} {X : Ω → Fin m → ℝ} {w : Fin m → ℝ}
    (hLp : ∀ a, MemLp (fun ω => X ω a) 2 μ) :
    variance (fun ω => ∑ a, w a * X ω a) μ
      = ∑ a, ∑ b, w a * w b
          * covariance (fun ω => X ω a) (fun ω => X ω b) μ := by
  have hX : ∀ a, MemLp (fun ω => w a * X ω a) 2 μ := fun a => (hLp a).const_mul _
  rw [variance_fun_sum hX]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

end EarthScience
