/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.M14CovarianceLinearMap

/-!
# Covariance-under-linear-map checks

Concrete consumers of `MathlibExt.Probability.M14CovarianceLinearMap`:
the identity map (`Cov(X) = Cov(X)`), the zero map (zero covariance),
and the public shape of both theorems. A numeric `2 × 2` check with
`Cov = [[4, 1], [1, 9]]` and `J = diag(2, 3)` is the off-diagonal
entry `2 * 3 * 1 = 6` of `J Cov Jᵀ`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Identity and zero maps
- B. Public shape

## iv. References

- `MathlibExt.Probability.M14CovarianceLinearMap`
-/

open MeasureTheory ProbabilityTheory

/-- Identity map: `Cov(1 · X) = Cov(X)` entrywise. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} {X : Ω → Fin m → ℝ}
    (hLp : ∀ a, MemLp (fun ω => X ω a) 2 μ) (i j : Fin m) :
    covariance (fun ω => Matrix.mulVec (1 : Matrix (Fin m) (Fin m) ℝ) (X ω) i)
        (fun ω => Matrix.mulVec (1 : Matrix (Fin m) (Fin m) ℝ) (X ω) j) μ
      = ∑ a, ∑ b, (1 : Matrix (Fin m) (Fin m) ℝ) i a * (1 : Matrix (Fin m) (Fin m) ℝ) j b
          * covariance (fun ω => X ω a) (fun ω => X ω b) μ :=
  EarthScience.covariance_linear_map hLp i j

/-- Zero map: `Cov(0 · X) = 0` entrywise. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} {X : Ω → Fin m → ℝ}
    (hLp : ∀ a, MemLp (fun ω => X ω a) 2 μ) (i j : Fin m) :
    covariance (fun ω => Matrix.mulVec (0 : Matrix (Fin m) (Fin m) ℝ) (X ω) i)
        (fun ω => Matrix.mulVec (0 : Matrix (Fin m) (Fin m) ℝ) (X ω) j) μ = 0 := by
  have h := EarthScience.covariance_linear_map (J := (0 : Matrix (Fin m) (Fin m) ℝ)) (X := X) hLp i j
  rw [h]
  simp

/-- Public shape of the variance of a linear combination. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} {X : Ω → Fin m → ℝ} {w : Fin m → ℝ}
    (hLp : ∀ a, MemLp (fun ω => X ω a) 2 μ) :
    variance (fun ω => ∑ a, w a * X ω a) μ
      = ∑ a, ∑ b, w a * w b
          * covariance (fun ω => X ω a) (fun ω => X ω b) μ :=
  EarthScience.variance_linear_combination hLp
