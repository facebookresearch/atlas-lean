/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.GreensOperatorTrace
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for the trace of the Green's operator

* The first two Green's eigenvalues, and the square of the first.
* The two-term partial sum is already below the trace `1 / 6`.
* The Green's kernel on the diagonal: `G(x, x) = x * (1 - x)`,
  with `G(1 / 2, 1 / 2) = 1 / 4`.
* The trace formula, restated as a standalone check.
-/

open MathlibExt.Analysis.ODE.GreensOperatorTrace

namespace MathlibExtTest.Analysis.ODE.GreensOperatorTraceTests

/-- The first Green's eigenvalue is `1 / π²`. -/
example : (1 : ℝ) / (((1 : ℕ+) : ℝ) ^ 2 * Real.pi ^ 2) = 1 / Real.pi ^ 2 := by
  simp

/-- The second Green's eigenvalue is `1 / (4π²)`. -/
example : (1 : ℝ) / (((2 : ℕ+) : ℝ) ^ 2 * Real.pi ^ 2) = 1 / (4 * Real.pi ^ 2) := by
  have h2 : ((2 : ℕ+) : ℝ) = 2 := by norm_cast
  rw [h2]
  field_simp
  ring

/-- The square of the first Green's eigenvalue is `1 / π⁴`. -/
example : ((1 : ℝ) / (((1 : ℕ+) : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2 = 1 / Real.pi ^ 4 := by
  simp
  field_simp

/-- Every Green's eigenvalue is positive. -/
example (k : ℕ+) : 0 < (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2) := by
  positivity

/-- The two-term partial sum of the eigenvalue series is below the trace. -/
example : (1 : ℝ) / Real.pi ^ 2 + 1 / (4 * Real.pi ^ 2) < 1 / 6 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : (7.5 : ℝ) < Real.pi ^ 2 := by nlinarith [hpi, Real.pi_pos]
  have hpos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  field_simp
  nlinarith [hpi2]

/-- The Green's kernel on the diagonal is `x * (1 - x)`. -/
example (x : ℝ) : min x x * (1 - max x x) = x * (1 - x) := by
  rw [min_self, max_self]

/-- The Green's kernel on the diagonal attains `1 / 4` at `x = 1 / 2`. -/
example : min (1 / 2 : ℝ) (1 / 2) * (1 - max (1 / 2 : ℝ) (1 / 2)) = 1 / 4 := by
  norm_num [min_self, max_self]

/-- The trace formula, restated. -/
example :
    (∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) =
      ∫ x in (0 : ℝ)..1, min x x * (1 - max x x) :=
  greens_trace_formula

/-- The eigenvalue series sums to `1 / 6`, restated. -/
example :
    (∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) = 1 / 6 :=
  tsum_greensEigenvalues

/-- The squared eigenvalue series sums to `1 / 90`, restated. -/
example :
    (∑' k : ℕ+, ((1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2) = 1 / 90 :=
  tsum_greensEigenvalues_sq

end MathlibExtTest.Analysis.ODE.GreensOperatorTraceTests
